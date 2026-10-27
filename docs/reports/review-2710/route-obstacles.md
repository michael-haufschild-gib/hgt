# Hard mathematical obstacles: routes, candidates and supporting programmes

Status: 2026-10-27, corpus `6046e5478` with working tree. Scope: the 31 live routes, 17 standalone candidates, PW-B and the supporting programmes. Companions: [summary, next questions and new-field assessment](obstacles-summary.md), [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md).

## Evidence and classification

**Sources.** Route inventory: the [frontier map](../rh-current-frontier-map.md) and the [killed-routes catalogue](../rh-killed-routes.md). Statuses were researched with `scripts/formal_tools.py research` and by reading module docstrings and theorem statements in `formal/`; findings are recorded in `logs/review-2710-v4-research-log.md`. Nothing was compiled. Labels: `[L]` integrated source, `[S]` working or unintegrated source (as the frontier map marks it), `[P]` paper proof, `[R]` reading or model calculation of this review, not a theorem.

**Obstacle classes.**

- **(a) Just work.** Known mathematics suffices: finite certificates, certified computations, premise checks, transport of proved estimates, corollary assembly, sharp constants, imports of published theorems. IDs `W1`–`W21`, defined in the [summary](obstacles-summary.md#1-just-work). A just-work item may have an unknown outcome; what is known is the method.
- **(b) Open mathematics.** No known solution. Three tiers, defined in the [summary](obstacles-summary.md#2-open-mathematical-obstacles):
  - `B1.*`: RH-strength closing statements, each equivalent to RH or stronger;
  - `B2.*`: classical open problems weaker than RH;
  - `B3.*`: open problems isolated by this research, not known to be RH-equivalent.

**Notation.** `Δ = sup_ρ |Re ρ − 1/2|` (zero width), `Θ = 1/2 + Δ` (zero abscissa). A receiver bounded at rate `σ < 1/2` gives `Δ ≤ σ` (quasi-RH); RH is rate zero. `κ` is the pole order at `s = 1`, `d` the archimedean degree. For a zero `ρ` of multiplicity `m`: `ρ* = 1 − ρ̄`, depth `δ = Re ρ − 1/2`. `f̂(s) = ∫ f(u) e^{(s−1/2)u} du`.

- **Two forms.** `W` is Weil's form; `D(f) = Σ_ρ m_ρ |f̂(ρ)|²` the **collided form**; `Δ(f) = Σ_ρ (m_ρ/2)|f̂(ρ) − f̂(ρ*)|²` the **off-line defect**; `T_L` translation by `L`; `E_f(L) = D(T_L f) + D(T_{−L} f) − 2D(f)` the **Hecke defect**; `M_f = Σ_ρ m_ρ δ_ρ² |f̂(ρ)|²` the **moment of inertia**.
- **Electrostatics.** `E(p) = Σ_{q ≠ p} m_q/(p − q)` the **field** at a zero; `𝓔` the **transverse energy** of the distinct zeros.
- **Torsion.** `O_n` the primitive `n`-th roots of unity; `I(m, n)` their archimedean intersection; `c(n) = I(n, n)/φ(n)` the self-intersection; `P(m, n) = Λ(n/m)(n/m)^{−1/2}` (for `m ∣ n`, `m ≠ n`) **Weil's prime kernel**; `β(n, t) = c(tn) − c(n)` the Hecke cocycle; `K_q` the tower matrix, `q = p^{−1/2}`; `G_r` the archimedean lattice germ; `Λ₂ = Λ log + Λ ⋆ Λ`.
- **Atomic resolution.** An **atomic test** is `f = Σ_{n ≤ N} x_n g(· − log n)` with `g` a `C²` bump of width `w`; the atoms `log n` are `δ_N = log(1 + 1/N)` apart. `P_N(x) = Σ x_m x_n P(m, n)`; `u_n = n^{−1/2}` the **pole vector**; `ℓ(x) = Σ x_n n^{−1/2}` the **polar functional**; `M = arch − prime` the Markov form; `C(f) = ∫ f cosh(u/2)`, `S(f) = ∫ f sinh(u/2)`; `E_φ` the **self-energy of an atom**, `K_φ(c)` the **archimedean cross kernel** between atoms at log-distance `c`.
- **Other.** `σ_γ(s) = 1 + 2iγ − s`; `ζ_γ(s) = ζ(s)²ζ(s + iγ)ζ(s − iγ)`, class `HeightCoupledSystem 2 1 1 γ`; `ν_N` the torsion measure.

## 1. Facts that fix the present frontier

### 1.1 Two forms on the test space

| Form | Positive? | Hecke equivariant? | Computed by |
|---|---|---|---|
| Weil's form `W` | iff RH; finitely many negative directions at every aperture [L] | yes, for every zero configuration [L] | the explicit formula |
| Collided form `D` | yes; faithful; at each aperture the logarithmic Sobolev norm [L] | iff RH [L] | the `ξ` current and polynomially many integer theta values [L] |

- **Capacity identity** [L]. `Re W = D − Δ`; RH iff `W = D` iff `D` Hecke invariant iff one `T_L`, `L ≠ 0`, is a similitude of `D`.
- **Norm** [L]. `c ∫|f̂(σ)|² log(|σ| + 4) ≤ D(f) ≤ C ∫|f̂(σ)|² log(|σ| + 4)` at each aperture; Gårding; fewer than `2AT₀K/π` negative directions of `W` at aperture `A`; local Weyl law.
- **Computation** [L]. Integer theta prefixes recover the depth moments with error `O(n^{−2} + log n/n)` for `a + j|L| ≤ 2 log(n + 1)` and detect zeros in discs of radius `1/(16(n + 1)^6)`. The readings are integrals in `z` of finite theta prefixes, not finite quadratures.
- **Moment of inertia** [L]. `4L² M_f ≤ E_f(L) ≤ 8(cosh L − 1) M_f`, `E_f(L)/L² → 4M_f`.
- **Depth geometry and amplification** [L/S]. `L ↦ D(T_L f)` is the Laplace transform of the depth measure; two-scale rigidity `E(L)² ≤ D(E(2L) − 4E(L))`; Stieltjes moment problem; dyadic amplification with fixed loss `D(f)`. Amplification is **soft**: it holds for every finite nonnegative depth configuration, golden and fake data included [L].
- **The one-scale bound is a strip** [S]. `E_f(L) ≤ D(f)(2cosh(2ϑL) − 2)` for every test and scale iff every zero has depth `≤ ϑ` (`zeroFreeStrip_iff_heckeDefect_bound`). Integer prefixes transfer such caps without loss [L]; explicit all-`n` prefix errors give `4L²M_f ≤ reading + error` [S]; at the schedule `n_k = ⌊exp(2^k/2)⌋ + 1`, `Θ ≤ 1 − θ` iff every reading is `O((n_k + 1)^{2(1−2θ)+ε})`, and RH iff every reading is subpolynomial [S]. Vinogradov–Korobov gives readings `o(n²)` throughout the horizon [S], no power saving.
- **Reading [R].** What computes `D` and what its defect measures is answered; every uniform bound on the defect is a zero-free strip. A bound on `M_f` that is not a strip must depend on the test or be averaged.

### 1.2 Local type, elliptic localizers and the forcing gap

At an off-line pair the local form is `2 Re(u v̄)` in `(f̂(ρ), f̂(ρ*))`, signature `(1, 1)`.

| Type | Action on the fibre | Correspondences | Positivity of a cyclic span forces |
|---|---|---|---|
| Hyperbolic | boost, `\|β\| ≠ 1` | Hecke operators, archimedean flow, gauge twists, at off-line pairs | isotropy |
| Elliptic | rotation or swap | Hecke on the line; resonant dilations; `σ_γ`; rotations of the circle | only `Re(u v̄) ≥ 0` |
| Unipotent | identity on polar parts | the successor | nothing |

- **Resonance** [L]: a symmetric dilation by `a` is elliptic at an off-line ordinate `γ` iff `γ log a ∈ πℤ`. **Elliptic localizers** [L]: the stabilizer of an off-line pair among reflection-compatible affine maps is `{id, σ_γ}`; even sector `+2|G(ρ)|²`, odd sector `−2|G(ρ)|²`. **Symmetric squares** [L]: nonnegative symmetric-square spectra at one prime iff `Re ρ = 1/2`. **Sparse annihilators** [L]: `1 − T_p^N` kills only critical symbols on a lattice of heights.
- **Rotations of the circle** [L]. `R_ζ: z ↦ ζz` is exact for the Abel pairing (no anomaly) and diagonalizes it; on `μ_N` the rotation spectrum is the lattice germ at `k/N`, renormalized `−(ψ(k/N) + γ + log N)/N`. Rotations localize in the additive dual `ℚ/ℤ`; zero ordinates live in the multiplicative dual; an elliptic localizer for zeros cannot come from torsion rotations.
- **Conductor horizon** [L]. `Re W_ζ(e^{−iγu} f) ≥ 0` once `C + (4 + ε)e^a + 2 ≤ log(1 + |γ|/8)`; source-blind there.
- **Forcing half and gap** [L]. One odd-sector sign, a local count and depth dominance force a companion; the certificate needs `e^{2δa} > 768A log(|γ| + 3)`, disjoint from the horizon at every height.
- **Reading [R].** Beyond the horizon the detector's prime side is a prime polynomial of length `(log γ)^{O(1)}` at the zero's ordinate; its sign is the alignment of `γ log p`.

### 1.3 Electrostatics of the zero divisor

- **Computed field** [L]. `L(Λ ⋆ Λ, s) = (ζ′/ζ)²`; the simple Laurent coefficient at a zero is `2m` times the transverse field, completed by the archimedean term.
- **Virial laws and equilibrium** [L]. Newton, Stieltjes and transverse virial laws; reflection-closed finite configurations are in equilibrium iff critical; energy `0` or `≥ 1`.
- **Energy of the divisor** [L]. `𝓔 = 0` iff RH iff `𝓔 < 1`; `𝓔 < ∞` iff finitely many off-line zeros; work equals energy; source work exhausts the copy energy `𝓔_copy`.
- **Energy of one zero** [L]. Every off-line zero has `E(ρ) ≥ 1`; every zero has `E(ρ) ≤ 16(C + log(|γ| + 4))`; a window has energy at most `16(C + log(|T| + H + 4))` per zero. The energy is unconditionally logarithmic; the field is not controlled (near-coincident pairs).
- **Quantization** [L]. RH iff every unit window has energy `< 2`.
- **Field threshold** [L]. RH iff every right zero feels a transverse field `≤ 1`, iff (explicit `c`) every such field is `< √(2c log(|γ| + 4))`.
- **Terminals, rays, lens, Harnack** [L/S]. Every right zero has a terminal within `C log γ` with an outward zero-free ray carrying reserve `≥ m/h + m/(2a + h) + c·a·log γ`; zero-free lens [L]; Harnack on the Carathéodory region spreads the floor to discs with factor `1/3` [S].
- **Terminal ceiling is a strip** [S]. A ceiling excluding right terminals of depth `> a` is equivalent to the zero-free strip of width `a`; RH iff there is no right terminal.
- **External field** [L]. For `σ > 1`: `Σ Λ(n) n^{−σ} cos(γ log n) ≤ Re(Γ-part)′ − m/(σ − β)` at a zero `β + iγ`. No interior counterpart.
- **Selberg's source** [L]. `Λ₂ = μ ⋆ log² ≥ 0`, `L(Λ₂) = ζ″/ζ`; degree renormalization `m² → m(m − 1)`.
- **Gauge behaviour** [L]. Electrostatics is blind to the archimedean twist; the twisted source `ωΛ₂` is nonnegative at a prime iff `ω(p) = 1`.
- **Reading [R].** Equilibrium, quantization and the field are computed; uniform ceilings on terminals or on the Hecke defect are zero-free strips; the excluding inequality is a non-uniform upper bound of size `√log γ`.

### 1.4 Torsion intersection and renormalization: the regulator decides

- **`Λ` is an intersection number** [L]. `I(m, mt) = φ(m)Λ(t)`; `Λ(n) = log #(𝒪_{ℚ(ζ_n)}/(ζ_n − 1))`; every entry of the prime kernel is a log-order; orbit intersections are digamma sums at rational points [L/S].
- **Self-intersection** [L]. `c(n) = Σ_{p^a ∥ n}(a − 1/(p − 1)) log p`; along a `p`-tower it grows by `log p`. **The self-intersection dominates the tower** [L]: on each ladder the renormalized torsion form `−P − diag(c)` is negative definite above the second level (`Δ² < 0` for genus `≥ 2`, read prime by prime).
- **Local Hodge index and the local–global failure** [L/S]. `P = Σ_p L_p`, `L_p = log p (K_q − 1) ⊗ 1`, each two-sided bounded; the global prime form has no `ℓ²` ceiling. Summing the local bounds costs `238√M`; the joint Schur bound is `2 log N + O(1)`: summing local indices in absolute value is the square-root threshold.
- **Survival law** [L]. Positivity of a regularized family passes to the limit exactly on the null cone of the counterterm.

| Regulator | Counterterm | Survival | Hecke behaviour |
|---|---|---|---|
| Abel radius `r` on torsion | identity | `{0}`; limit indefinite on `{1, q}` [L] | anomaly `β(n, t) = log t − Σ_{p∣t, p∤n} log p/(p − 1)`, not a bounded coboundary [L] |
| Abel radius on the lattice germ | `𝟙𝟙ᵀ` | polar hyperplane `Σ c_i = 0` [L] | — |
| Spacing radius `e^{−ε/n}` | scalar `log(1/2ε)` | `{0}`; limit `−P + diag(tame different)` indefinite on `{1, 2}` [L] | covariant up to tame ramification [L] |
| Horizon `n ≤ N` (Weil's form) | rank one and polar on uniform log-scale profiles [S]; identity on the `p`-valuation classes, unbounded rank [S] | polar-neutral step profiles bounded; no fixed number of linear constraints removes the divergence [S] | covariant; covariant counterterm `κ_N ∈ [log N − log 8 − 4, log N + log 4 + 4]` [S] |

- **Coupled survival law** [S]. For a PSD coupled counterterm `[[A, C], [Cᵀ, D]]` with injective prime block, no pure prime vector survives and the prime projection of the survival space has dimension at most `rank D`: a partner pays at most as many prime directions as the rank of its own counterterm. Every positive family keeping the Abel torsion block has `A = cI`.
- **The archimedean place pays the arithmetic point** [S]. Ramanujan modes with any number of constant-mode archimedean nodes give the counterterm `[[1, e₁𝟙ᵀ], [𝟙e₁ᵀ, 𝟙𝟙ᵀ]]`; prime survival is `ℝe₁`; no orbit of order `≥ 2` survives.
- **Ramanujan twins** [L]. Survival cone = per-order relations; the pole-node block is the torsion energy with limit `−φ(m)Λ(t)`; pole-node completion is PSD but at infinite node height regenerates a full-rank counterterm `φ(m) log u` with survival `{0}`.
- **Covariance forces a scalar** [S]. `−P + diag(h)` is Hecke covariant iff `h` is constant on orders; a scalar counterterm has survival `{0}`.
- **The anomaly costs half a logarithm** [S]. Every torsion counterterm (keeping `c(n)`) is `≥ (3/2) log N − C`; the covariant one is `log N + O(1)`. Weil's prime sum, which drops the diagonal, is the anomaly cancellation.
- **Gauss digamma** [L]. Torsion energy on `μ_N` and the lattice germ at `k/N` are Fourier dual; `log N` is the anomaly of `[N]`.
- **Reading [R].** The rank of a counterterm is a property of the regulator. No regulator of the prime place alone keeps positivity: Abel leaves `{0}`, spacing is covariant and indefinite, the horizon diverges along every torsion orbit. Coupling cannot lower the torsion rank. The prime divergence at the horizon is the identity on the arithmetic factor times `log N`, which is the shape of the archimedean self-energy: the archimedean place is the covariant counterterm.

### 1.5 Atomic resolution: the archimedean place pays the prime place

- **Weil's prime functional is the finite intersection** [L]. For log-atom tests of width `δ < log(1 + 1/M)`, only exact ratios `m/n` are seen and the prime sum is `‖φ‖² Σ_p Q_p(x)`.
- **The polar part pairs the pole direction** [L]. Polar part `= 2αβ ℓ(x)(Σ x_n n^{1/2})`, rank two, signature `(1, 1)`.
- **Hodge index in tower coordinates** [L]. `Re(arch + polar) = E_φ|x|² + 2αβ ℓ(x)(Σ x_n √n) − Σ_{m<n} x_m x_n K_φ(log(n/m))`, with `E_φ ≥ ‖φ‖²(γ₀ + e^{−1/2} log((1 − δ)/δ))`; under RH the towers plus archimedean couplings are paid by self-energy plus polar pairing. The direction "RH ⇒ inequality" is a receiver.
- **Stability law** [L]. `M(f) ≥ (2θ′(0) + e^{−1/2} log(δ_N/(2w)) − 2 log N − log 4 − 4) ∫f²`; `M ≥ 0` for `w ≤ atomicWidth N = N^{−O(1)}`.
- **Coupled form at atomic resolution** [S]. `Re W = M + 2C² − 2S²`; `Re W + 2S² ≥ 0` on atomic tests of width `≤ atomicWidth N`; `Re W ≥ 0` on `|S| ≤ |C|`, in particular for nonnegative weights. A rank-one counterterm couples the two places and the pole.
- **Gauge invisibility** [L]. `P_ω(m, n) = ω(m)ω(n)P(m, n)`; every sign twin's atomic form is ζ's in the gauge `x ↦ ωx`; the stability law holds for every twin. The finite intersection is gauge blind; selectivity can come only from the pole term and the archimedean place at overlapping widths.
- **Reading [R].** The leading constants match: covariant prime counterterm `log N + O(1)` against archimedean self-energy `log(1/w) + O(1)` at `w ≍ 1/N`. The corpus's `N^{−O(1)}` width comes from the lossy Lévy constant `e^{−1/2}` and from discarding shifts beyond `δ_N`. With the sharp constant, the RAPT ceiling and a Schur bound on `K_φ` (row sums `≲ 4wN(1 + log N)`), the norm estimate `E_φ − ‖P‖ − ‖K‖ > 0` should hold at `w ≍ δ_N/(C log N)` (W9). At `w = cδ_N` with `c` fixed the norm estimate fails: `K` is of size `c log N` on vectors concentrated near scale `N`, where `P` is small, and `P` is of size `log N` on spread vectors, where `K` is `O(c)`; a joint estimate is needed (B3.25). Beyond the spacing the atoms overlap, non-ratio lags `log k` enter the prime sum, and the gauge becomes visible (B3.26). The spacing scale is the Montgomery–Vaughan regime `T ≍ N` of Dirichlet polynomials of length `N`, where off-diagonal Hilbert terms are as large as the diagonal.

### 1.6 Weil's argument over `ℤ`, layer by layer

| Layer | Over `𝔽_q` | Over `ℤ` | Forces the sign? |
|---|---|---|---|
| L1 Identities | Lefschetz, adjunction | exact | no (golden datum) |
| L2 Theorem of the square | graph map quadratic | free for normalized graphs | no |
| L3 Budget | `δ(Δ, Δ) = 2g` | free | no |
| L4 Kernel counts | `#ker ≥ 0` | collided (complex fake: counts `≥ 0`, Rosati `−2304`) | collided only |
| L5 Rosati positivity | polarization | `⇔` RH | missing |
| L5′ Counting origin | RR on `C × C`; Stepanov | each counting currency is RH; Stepanov needs a lattice spectrum | each is RH |
| L5″ Diagonal | `2 − 2g`, finite | regulator-dependent; no prime-only regulator keeps positivity; at atomic resolution the archimedean self-energy pays with a rank-one pole counterterm [L/S] | missing beyond atomic resolution |
| L5‴ Local–global | one Frobenius ladder | transverse ladders; local Hodge index at each prime; no `ℓ²` ceiling | missing: archimedean payment at the spacing scale |
| L5⁗ Base | all places act on one ladder, towers overlap at `lcm` lags | ladders of distinct primes never share a pair; the successor is transverse to every ladder [S] | missing: a common base |
| L6 Amplification | fixed tensor loss | fixed tensor loss `⇔` RH; dyadic amplification soft | missing |

**Calibration over `𝔽_q`** [L]. Odd-degree hyperelliptic RH by counting, split case included; Hasse; effectivity functions and naive heights exist there. **Completion law** [L]. `|τ|² = q` by counting; Pólya–Vinogradov; Burgess; least non-residue `≤ p^{1/(4√e)+ε}`; the arithmetic point has no period; Nair's floor.

### 1.7 Counting is the sign

- Section counts with RR and Bézout, effectivity functions, naive heights, convex heights, fixed tensor loss, horizon torsion at `√N` precision, the one-sided count `ψ(x) − x ≤ C√x log²x` and the Farey sum at `√N` are each RH [L].
- The polar box count is an effectivity function iff Hodge; subtracting prime-power nodes destroys RI [L]. Theta-surface counts are fibre-independent; lattice counts give `ζ(s₁ + s₂)` or `ζ(s₁)ζ(s₂)`; Jacobi–Hurwitz packets are blind or inflate; RH iff a bounded-below asymptotic subquadratic height exists [L].

### 1.8 Budget currencies

| Row | Over `ℤ` | Over `𝔽_q` |
|---|---|---|
| Prime error | linear log-energy budget iff RH; slope `≥ 2 + γ_E − log 4π`; Abel slope at the genus iff RH with simple zeros [L] | slope `Σ mult(β)²` [L] |
| Mertens | budget ⇒ RH, simple zeros, `Σ\|ρζ′(ρ)\|^{−2} ≤ S` [L]; converse not formalized | purity with simple spectrum; strict Hasse in genus one [L] |
| Successor shift | `D_Λ(s)/s ∈ H²(Re s > 1/2)` [L] | — |

### 1.9 The gauge principle

- **Orbits** [L]. Multiplicative data determine a source up to its gauge orbit; the Möbius half-power law holds Haar-a.e., fails at the Liouville twin, is RH at the gauge point `0`.
- **Charged couplings** [S]. A coupling `(n; a, b)` is blind under every real sign gauge iff `nab` is a square; successor couplings are charged; dyadic cell dilation is covariant only at the Euler gauge, reaching `ω(p) = 1` for `p ≤ 2X + 1`.
- **Cell holonomy** [L/S]. The Hilbert–Schmidt covariance defect of the dyadic cell dilation is at least twice the number of charged cells; at Liouville the charged cells are `{a : λ(a) = λ(2a + 1)}` [L]; for every real sign gauge flipping `2`, at least `K` charged cells lie below `162(K + 1)^4`, so the defect grows at least like `X^{1/4}` [L]. Reading [R]: positive logarithmic density `1/2` of `{a : λ(a) = λ(2a + 1)}` follows from Tao's two-point logarithmic Chowla theorem (`a₁b₂ − a₂b₁ = 1 ≠ 0`); lower natural density is two-point Chowla, open.
- **Coefficient margin** [L]. At a flipped prime, `Λ₂(p) − ωΛ₂(p) = 2 log² p`; on every window some `n ≤ N` has `ωΛ₂(n) ≤ −log² 2`: the coefficient margin never collapses as primes enter. It is not a margin on signed tests.
- **Gauge invisibility below the spacing** [L]. §1.5.
- **First windows** [L]. At `181/500` and `23/40` the Liouville and `{2}`-flipped twins fail on witnesses where `ζ` is positive; the Liouville ground eigenvalue stays `< −3/10` at every aperture `≥ 23/40`; nine-modulus collar and Catalan `(8, 9)` separator at `2 log 2`. The full floor of `ζ` at `23/40` is uncertified.
- **Repulsion; worst twin** [L]. `(1 + cos(γ log 2)) + (1 + cos(γ log 3)) ≥ e^{−|γ|}/50`; on nonnegative tests `Re W_Λ ≤ Re W_w` for `w ≤ Λ`.

### 1.10 Positive systems: one variable, polar configurations, deformations

- `CompletedPositiveSystem 1 d = ℝ^× · ζ`; pole order pays inserted zeros; quartets contract only against a real anchor; anchored quartet `⇒ κ ≥ 3`; planting `Δκ ≥ 2`; Fejér barrier; no analytic global collision carrier [L].
- One section decides positivity; independent-ordinate packets buy at most their pole share; harmonic packets `M` times it; every finite lattice cloud has a finite purchase bound (minimal maximal height over admissible weights), with no uniform bound for growing clouds [S].
- Landau–Wronskian principle; Abel–Gram law; positive deformations form a monoid without nontrivial units [S]; the coupled class is not rigid at critical-zero ordinates; positive rigidity, chirality and central ceilings at `γ` are the absence of (off-line) zeros at `γ`; surplus residues are even central drops `≤ 2 ord ξ`; ceilings transfer to factors [L].

### 1.11 Escape

RH iff admission at every damping iff positive gauge mass of every escape state; energy-rate law both directions; Abel atoms; capacity, endpoint, shadow and infinite-height laws; escape forms collided. Escape classifies, it does not exclude [L].

### 1.12 Positivity: pointwise, averaged, statistical, quantized; zero ordinates

- Windows: full `‖f‖²/5000` and odd `‖f‖²/1000` through `181/500` [L]. Short-cycle positivity at lag `log 2`: for even `g` supported in `[−η, η]`, `η ≤ 181/500 − (log 2)/2`, `Re W(g − T_{log 2}g) ≥ ‖g − T_{log 2}g‖²/1000` [L].
- Averaged positivity on `Γ^{99/100} ≤ H ≤ Γ/8`; zero-ordinate positivity; positive proportion of heights; census: `(2/3 − ε)N + M_off ≤ N₀ˢ`, `≥ 4/5` of ordinates critical, `≥ 3/4` of copies within `4/log T` [L].
- **Alignment counts at zero ordinates** [L]. Discrete mean value over zero copies in `(A, A + R]`: `Σ_γ |F(γ)|² ≤ K log(A + R + 1)(R + 8N(1 + log N))(2 + log² N) Σ|a_n|²`. A prime polynomial of length `X` reaches `(1 − η) log T` at `O(T log⁴ X/log T)` zero ordinates; higher moments give `T^{1 − 1/C + o(1)}` at `X = (log T)^C`. Counts allow exceptional zeros; no implication "off-line ⇒ aligned" is proved.
- **Zero moments are Rosati pairings** [L]. Landau–Gonek sums `Σ m_ρ (QQ̃)^k(ρ)` are `|Q(ρ)|^{2k}` on the line and `2 Re(Q(ρ) conj Q(ρ*))^k` for an off-line pair. Their positivity for all `Q`, `k` is a Hodge index of Weil type, not an input.
- Aperture ceiling `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})`; ground rate = polar rate = width without clustering; form-norm rates = width [L].

### 1.13 Realization and duality

Maximal sharp-stable positive Meyer ideal = off-line-blind ideal; coupled point-stable carriers isotropic; positive self-dual measures with a gap are Dirac combs; affine positivity on `Aff(ℚ)` is induced from dilations; Hecke states positive definite iff `s ≥ 1/2`; every nonzero `L²` wave has a visible successor; atomic spectra stay blind [L].

### 1.14 The width currency

For `0 < θ ≤ 1/2` the following are equivalent [L]: escaped Möbius pairings `Σ_{(N−b)/a < j ≤ N} μ(j)/j` decay at power `θ` uniformly in `N, a, b`; the dyadic case; receiver damping rate `≤ 1/2 − θ`; `Θ ≤ 1 − θ`; the all-test Hecke strip cap at depth `1/2 − θ`; dyadic defect growth at rate `1 − 2θ`; `Re ξ′/ξ ≥ 0` on `Re s > 1 − θ` (graded Lagarias). Seven quasi-RH criteria (escaped, dyadic, centred prime band, short-window prime and Möbius savings, receiver below half, `Θ < 1`) are equivalent. Unconditionally the escaped pairings vanish at the Vinogradov–Korobov rate `C exp(−κσ(M)/48)` uniformly in `N, a, b` [L]. The coalescent parametrization `θ(λ) = (λ − 1)/(2λ)` names `θ(4/3) = 1/8`, i.e. `Θ ≤ 7/8`, an open quasi-RH target. Reading [R]: the decay is classical (PNT, VK), the equivalences are classical in substance; the module fixes one currency across five programmes and supplies no strip.

**Every unconditional positivity in the corpus is one of:** invariant (blind, half-blind, isotropic); averaged or statistical; non-localizing; on nonnegative tests; collided; twisted below the conductor horizon; a finite-window certificate; local at one prime; carried by a counterterm whose survival cone is `{0}`, a hyperplane or the arithmetic point; coefficient positivity of a source; a zero-side reserve; **atomic: below the spacing scale, where it is gauge blind**.

### 1.15 Thresholds where proved positivity stops

| Threshold | Proved below | Open at or beyond |
|---|---|---|
| Conductor horizon `e^a ≲ log γ/4` | twisted positivity, source blind | the odd-sector sign; forcing needs `e^{2δa} > 768A log γ` |
| Atomic width vs spacing `δ_N` | `M ≥ 0`, `Re W + 2S² ≥ 0` at `w ≤ N^{−O(1)}`, gauge blind | `w ≍ δ_N`, then overlap, where non-ratio lags and the gauge enter |
| Square-root threshold | Landau–Gonek moments from primes; local Hodge indices summed (`√M` price) | Rosati products beyond it; coalescent surplus; joint multiplicative structure |
| Half damping `ε = 1/2` | all receivers bounded | signed sub-half control |
| Apertures `181/500`, `23/40` | certified floors and separations | all apertures; margin laws |
| Vinogradov–Korobov | sub-power savings | any power saving (quasi-RH) |
| Short windows `Γ^{99/100}` | averaged positivity | `Γ^{1/2+ε}` (W7), below `1/2` (B2.10) |
| Detector length `(log T)^C` | power-saving alignment counts | an individual zero |

## 2. The 31 routes

Each entry: status; (a) just work; (b) open; walls ([walls ledger](walls-ledger.md)).

### WL — Weil lag function
**Status.** Spline, lag, deficit, critical-energy and cross-work receivers read `Δ`; RH ⇔ critical energy bounded; high zeros contribute `O(1)`; RH ⇔ `ψ(x) − x ≤ C√x log²x` eventually ⇔ horizon torsion ⇔ the Farey sum at `√N`; RH ⇔ a linear prime-error budget; RH with simple zeros ⇔ the Abel slope tends to the genus; filtered deficit `Γ^{−1/2}`.
**(a)** Averaged bounded-energy statement (W18); windows `Γ^{1/2+ε}` (W7); finite budgets (W2); census transport (W14).
**(b)** Signed lag cancellation at every slack (B1.1); an actual budget (B1.10); selection (B1.4); quasi-RH (B2.1).
**Walls:** 1.0, 1.1, 1.15, 1.19, 3.14.

### RW — Restricted Weil ground energy
**Status.** RH ⇔ `μ(A) > 0` for all `A`; the flow never stalls; RH ⇔ cumulative relaxation `≤ μ(3/10)`; ground rate = polar rate; Gårding and finite negative index; floor `1/5000` through `181/500`; no positive exponential floor.
**(a)** Certified floors past `181/500` (W5); one rate dictionary with SRT and ACS (W18); transport of census and moment-of-inertia law (W4).
**(b)** Zero negative index at every aperture (B1.3); signed shell flux (B3.4); `polarRate = Δ` for clustering zeros (B3.1); selection (B1.4).
**Walls:** 1.3, 1.11, 1.13, 3.2, 3.14.

### FU — CCM-FU signed prime scheduling
**Status.** Both one-sided bounds of the completed Möbius–divisor Abel moment are RH-equivalent; terminal primes realize graph sources; the isolated critical prime channel is negative on narrow windows, not on dyadic windows [S].
**(a)** Finite schedules (W2); wide-window premises (W3).
**(b)** Complete-history signed cancellation (B1.1).
**Walls:** 1.1, 1.6, 3.2, 3.4.

### RP — Route-P / SP-E history floor
**Status.** An eventual floor on the matched-quantile history is RH-equivalent; hyperbola, centroid, square-debt identities and low-LCM payment proved.
**(a)** Finite floors (W2); low-LCM transport (W4).
**(b)** Full-history floor with high-LCM pairs, moving core and singular transport (B1.1).
**Walls:** 1.1, 1.8, 3.6.

### PA — Prime–archimedean source passivity
**Status.** Current, Bernstein-mismatch and signed-moment receivers RH-equivalent; each fixed Hausdorff order positive beyond its shift threshold.
**(a)** Explicit fixed-order thresholds (W5); finite blocks (W2).
**(b)** Order-uniform thresholds (B3.10); all-order passivity (B1.5).
**Walls:** 1.5, 1.6, 14.1.

### MC — Möbius cancellation at half power
**Status.** `M(x) = Ω±(√x)`; `ν̂_N(1) = M(N)`; RH ⇔ `M(N) = O(N^{1/2+δ})` ∀`δ`; a linear Mertens budget forces RH, simple zeros and summable residues; bands ⇔ `Θ < 1`; the width currency of §1.14 with VK-rate escaped decay uniform in `N, a, b`; Pólya–Vinogradov, Burgess, least non-residue; multi-modulus Kloosterman dispersion and simultaneous omitted-class correction; integer-theta prefix readings: `Θ ≤ 1 − θ` iff readings `O(n_k^{2(1−2θ)+ε})` [S].
**(a)** Mertens converse under RH and `J_{−1}(T) ≪ T` (W18); finite budgets (W2); VK as a growth-to-forcing instance (W16).
**(b)** Square-root cancellation at `0` (B1.1); an actual Mertens budget (B1.10); quasi-RH, e.g. `Θ ≤ 7/8` (B2.1); power-saving sign correlations (B2.6); a gauge-charged statistic at `0` (B3.15); growing-packet compensation (B3.6).
**Walls:** 1.0, 1.1, 1.12, 1.18, 1.19, 1.20, 3.10.

### TT — Theta tail and heat–Cassini currents
**Status.** Directed Wold receiver; RH ⇔ the bound at every `t ∈ (0, 1/2)`; restricted current signs and light-cone positivity.
**(a)** Finite covariances (W2); ACT/OWU transport (W4).
**(b)** Signed nonlocal covariance, i.e. complete odd Weil positivity (B1.3).
**Walls:** 1.3, 1.6, 3.4.

### LA — Line anchor
**Status.** RH ⇔ all-height head coefficient positivity at fixed `R² ≥ 1/2`; every positive heat repairs high heads; `0 ≤ Λ < 1/8` for the de Bruijn–Newman constant in the corpus normalization `H_t = ∫Φ(x)e^{tx²}e^{izx}dx` (Rodgers–Tao and Ki–Kim–Lee; standard normalization `0 ≤ Λ < 1/2`) [L].
**(a)** Explicit residual region (W18); finite heads (W2); import of the Polymath bound `Λ ≤ 0.2` (standard), `0.05` in corpus normalization (W18).
**(b)** Zero-heat sign on the residual region (B1.5, B3.7); de Bruijn–Newman bounds beyond the literature (B2.9).
**Walls:** 1.2, 1.6, 1.14.

### TG — Topological sub-unit gate
**Status.** Anchored cubic trace = winding; an integral nonnegative residual below one vanishes; residual sign and sub-unit bound not derived.
**(a)** Disc-wise traces (W2); Gaussian covariance transport (W4).
**(b)** Residual sign and sub-unit bound for a pre-divisor source (B1.6).
**Walls:** 1.2, 14.3, 14.8.

### HF — Positive Hodge form on arithmetic cohomology
**Status.** `D_idx` even when finite, RH ⇔ `D_idx < 2`; Lefschetz and symmetric-square receivers; counting currencies (§1.7); two forms and the moment of inertia (§1.1), one-scale cap = strip, prefix readings; electrostatics (§1.3) with logarithmic energy of each zero, terminal ceiling = strip, Harnack; torsion and the three regulators (§1.4), coupled survival law, covariance law, anomaly cost; atomic resolution (§1.5): stability law, rank-one coupled form, Hodge index in tower coordinates; zero moments are Rosati pairings; alignment counts (§1.12).
**(a)** Copy versus distinct energy (W13); quadrature of readings (W8); atomic stability up to a logarithm of the spacing (W9); `κ_min` constant (W11); overlap bookkeeping (W12); transport into HF coordinates (W4).
**(b)** The Lefschetz part / zero negative index (B1.3); `D_idx < 2` (B1.7); counting forms (B1.9); equivariance of `D` (B1.11); field and energy forms (B1.13); finite off-line index (B2.2); compatible families (B3.8); form positivity of `Λ ⋆ Λ` (B3.17); a non-uniform bound on `M_f` (B3.21); a selective polarization (B3.23); alignment (B3.24); spacing-scale joint estimate (B3.25); overlap regime (B3.26); covariant regulator with a null cone (B3.28); the base (B3.29).
**Walls:** 1.3, 1.4, 1.16, 1.17, 1.21, 3.13, 3.20, 3.22, 3.23, 3.24, 3.25, 14.2, 14.4, 14.18, 14.21, 14.24, 14.26–14.30.

### CHMD — Causal hyperbolic–modular duality
**Status.** Odd energy nonnegative iff no odd bound state above `1/2`; completion, cuts, domains and nodal convergence proved.
**(a)** Domain premises (W3); RW/SZ transport (W4).
**(b)** The nodal inequality, i.e. odd Weil positivity (B1.3).
**Walls:** 1.3, 3.3, 3.4.

### TH — Theta moment positivity
**Status.** All-rank strict positivity on the orthant at small time; fixed-rank coercivity; rank-`N` tests blind above height `O(N√log N)`.
**(a)** Explicit fixed-rank regions (W5).
**(b)** Signed coefficients at all degrees under one heat time (B1.5); decoupling rank from time (B3.10).
**Walls:** 1.6, 3.11.

### RN — Theta renewal and singular comparison
**Status.** A compact cone-positive renewal operator realizes the denominator through `det₂`; cone positivity does not confine resonances.
**(a)** Finite packets (W2); `det₂` transport (W4).
**(b)** Boundary-current orientation for the actual source (B1.6).
**Walls:** 1.2, 14.1, 14.3.

### WD — Ward orientation and horizontal collision
**Status.** Global cap vanishes iff RH; collision masses even; Hermite barrier, optimal heat and large-height repair formalized.
**(a)** Residual region (W18); finite heads (W2).
**(b)** Cap vanishing (B1.6); residual heat sign (B1.5).
**Walls:** 1.2, 1.14, 3.8.

### LI — Paired Li and prime–Gamma balances
**Status.** RH ⇔ subexponential lower floors at every positive rate; reciprocal-depth rates `≤ 1/431`.
**(a)** Finite floors (W2); constants (W5).
**(b)** The subexponential floor (B1.7).
**Walls:** 1.5, 3.8.

### SZ — Suzuki screw and shifted-kernel limits
**Status.** Compact-`L²` first variation = extended Weil energy; RH ⇔ nonnegative first variation on RH-complete tent families.
**(a)** Limit-family premises (W3); RW transport (W4).
**(b)** The first-variation sign (B1.3).
**Walls:** 1.3, 3.3, 3.6.

### PM — Physical-model Haar approximation (FZZ-P)
**Status.** RH ⇔ admission at every damping ⇔ positive gauge mass; energy-rate law; Abel atoms; infinite-height laws; escape forms collided.
**(a)** Cofactor premises (W3); transport of VK-rate decay and Kloosterman dispersion (W4); working sources (W19).
**(b)** Signed small-damping energy (B1.2); infinite-height escape (B3.2); inverse coercivity (B3.3); sub-half control (B3.9); paid ideal on escape (B3.12).
**Walls:** 1.8–1.10, 3.7, 3.12, 3.15.

### JAS — Joint ancestry
**Status.** Positive level-one budget ⇔ half-plane bound; half-power endpoint is RH; Gamma–theta source admitted; unconditional positivity reaches a logarithmic prime budget.
**(a)** Finite budgets (W2).
**(b)** The half-power budget (B1.1); quasi-RH (B2.1).
**Walls:** 1.0, 1.1, 3.4.

### CTF — Chronological tail and Báez–Duarte approximation
**Status.** Residual = `(1 − readout)² + centred energy`; RH ⇔ both small; floor `κ/log N`.
**(a)** Finite dilates (W2).
**(b)** Readout and energy together (B1.2); quantitative reconstruction (B3.3).
**Walls:** 1.8, 1.10, 3.12.

### HCF — Gaussian heat trace
**Status.** Positivity of both literal grids (`log 2`, `log 3`) at all degrees is RH-equivalent; one grid aliases.
**(a)** Finite-degree signs (W2).
**(b)** Both grids at all degrees (B1.5).
**Walls:** 1.6, 3.4, 3.11.

### XN — Xi Newton invariant discs
**Status.** Line-centred Newton discs covering every zero ⇔ RH; the margin is subharmonic.
**(a)** Finite covers (W2).
**(b)** Covering discs with nonnegative margin (B1.5).
**Walls:** 1.2, 3.2, 14.3.

### BAG — Deterministic zeta self-return
**Status.** Strong, local and cutoff-uniform recurrence each RH-equivalent; recurrence exactly at non-zeros.
**(a)** Threshold-law transport (W4).
**(b)** Returns near possible zeros (B1.7).
**Walls:** 1.2, 3.2.

### EWU — Even pole-weight uniqueness
**Status.** Blind minima nonnegative at every aperture ⇔ RH; source selection; finite-level existence ⇔ RH; floor `1/5000` through `181/500`, shared by every weight with `w(2) = log 2`.
**(a)** Certified floors (W5); margin table (W6).
**(b)** Low and mixed modes (B1.3).
**Walls:** 1.3, 1.4, 3.3.

### GTA — Transverse Schur charge
**Status.** Uniform quartic Schur decay RH-equivalent; an off-line zero forces a late positive charge floor.
**(a)** Finite truncations (W2).
**(b)** Rank-uniform decay (B1.5).
**Walls:** 1.6, 3.2.

### OWU — Odd Weil-weight uniqueness
**Status.** Odd positivity RH-equivalent; light-cone variation positive; at `181/500` and `23/40` the Liouville and atom-2 twins fail on witnesses where `ζ` is positive, permanently from `23/40` on; nine-modulus collar at `2 log 2`; short-cycle positivity at lag `log 2` with midpoint parity transposition [L]; companion certificate and conductor horizon disjoint; zero-side reserve and exterior law at the same ordinates; alignment counts at zero ordinates [L].
**(a)** Full floor at `23/40`, margin table of the `{2, 3}` twins, the `{2, 3, 5}` window (W5, W6); interior reading of the reserve (W10); exceptional-set accounting (W21).
**(b)** Odd Weil positivity (B1.3); gauge form-margin (B3.16); odd-sector sign beyond the horizon (B3.20); alignment (B3.24); overlap regime (B3.26); terminal control off a sparse set (B3.27).
**Walls:** 1.3, 1.18, 1.21, 3.4, 3.19.

### PBM — Regularized prime/log-ζ abscissa
**Status.** Half-plane bound at `α` ⇔ convergence on `Re s > 1/2 + α`; RH is `α = 0`.
**(a)** Width-functor transport (W4).
**(b)** Quasi-RH (B2.1); critical cancellation (B1.1).
**Walls:** 1.0, 1.1.

### RB — Robin/Nicolas
**Status.** Eventual Robin ⇔ Robin on colossally abundant numbers; counterexamples need growing lcm cores.
**(a)** Finite verifications (W2).
**(b)** The eventual Robin tail (B1.7).
**Walls:** 1.1, 1.6.

### SRT — Prime-side one-parameter lag localization
**Status.** One fixed-width late-lag family decides RH; smooth detector at aperture `Cδ^{−2}(4 + |γ|)²`; single-height phase-selective law; eventual all-height saving refuted; one- and two-prime Lefschetz receivers are the strip; detector = odd sector of `σ_γ`; conductor horizon; forcing gap; exterior law; terminal lens; Kronecker dilution; alignment counts at zero ordinates with power saving [L]; short-cycle positivity at lag `log 2` [L].
**(a)** Rate dictionary (W18); interior reading of the reserve (W10); exceptional-set accounting (W21); windows `Γ^{1/2+ε}` (W7).
**(b)** Selection (B1.4); critical cancellation (B1.1); Weil positivity (B1.3); counting forms (B1.9); near-coincidence beyond `½ log Γ` (B3.14); odd-sector sign beyond the horizon (B3.20); alignment (B3.24); terminal control off a sparse set (B3.27).
**Walls:** 1.17, 1.21, 3.1, 3.2, 3.14, 3.19.

### ACT — Arithmetic criticality / single-shift variation
**Status.** One fixed shift against all even compact profiles decides RH; light-cone kernel positive; sub-unit collar paid for `log d ≤ a − R`.
**(a)** Collar constants (W5); TT/OWU transport (W4).
**(b)** The uniform all-profile collar, i.e. Weil positivity (B1.3).
**Walls:** 1.3, 3.1, 3.4.

### AIP — Arithmetic incidence positivity
**Status.** Allocation for all tests ⇔ RH; shared-budget descent; joint `2, 3` payment at `23/40`; nine-modulus ledger; linear diagonal reserve cancels on the polar-neutral hyperplane; raw continuum towers have negative edge energy `≥ c e^A`. Atomic resolution (§1.5): the prime functional is the finite intersection; polar part rank two; tower-coordinate Hodge index; stability law; `Re W + 2S² ≥ 0` [S]; gauge invisible. Horizon (§1.4): polar on uniform profiles, unbounded rank on valuation classes [S]. Square-class couplings blind; cells charged.
**(a)** Certified joint payments at larger apertures (W5); atomic stability to `δ_N/(C log N)` (W9); overlap bookkeeping and finite-`N` certificates (W12); premises for the pole-neutralized form (W3).
**(b)** Weil positivity (B1.3); prime-weighted shared budget for the pole-neutralized continuum form (B3.6); spacing-scale joint estimate (B3.25); overlap regime (B3.26); the base (B3.29).
**Walls:** 1.3, 3.4, 3.21, 3.23, 3.24, 3.25.

### ACS — Arithmetic Castelnuovo–Severi effectivity
**Status.**
- Source RR; Meyer RR + Bézout; maximal blind ideal; isotropy; non-localizing positivity; Lefschetz receivers; Weil's layers (§1.6); faithful degree needs RH + simple zeros.
- Counting (§1.7); one-variable systems and deformations (§1.10); two forms, electrostatics, torsion, atomic resolution (§1.1–§1.5); census and alignment counts (§1.12).
- Selberg's source with gauge margin `2 log² p`; torsion adjunction, log-orders, rotations, spacing regulator, tower-coordinate Hodge index.
**(a)** Selectivity battery (W1); ceilings as central nonvanishing and quantization in ACS coordinates (W18); contraction last items (W17); `κ_min` constant (W11); working sources (W19).
**(b)** Forcing for a realization (B1.6); faithful branch (B1.8); counting forms (B1.9); equivariance of `D` (B1.11); ceilings and chirality (B1.12); field forms (B1.13); collar equality (B3.13); `Λ ⋆ Λ` form positivity (B3.17); full coupled class (B3.22); selective polarization (B3.23); spacing scale and overlap (B3.25, B3.26); covariant regulator (B3.28); the base (B3.29); `3/4` (B2.5).
**Walls:** 1.3, 1.15–1.18, 1.21, 3.8, 3.14, 3.18, 3.23–3.25, 14.4, 14.8, 14.10–14.30.

## 3. The 17 candidates and PW-B

A candidate lacks an independent source construction or landing; each faces B1.6. These theorems constrain every candidate:

- single-channel sharp-stable positivity certifies only blindness; coupled point-stable positivity only isotropy; non-localizing positivity holds for every prime weight;
- multiplicative correspondences act hyperbolically at off-line pairs; elliptic localization is resonance; `σ_γ` is the only reflection-compatible affine localizer, its certificate separated from the conductor horizon; rotations of the circle have archimedean spectrum and cannot localize zeros;
- positivity on nonnegative tests is shared by dominated twins; square-class couplings, the finite intersection and every atomic-resolution form are gauge blind;
- finite multiplicative certificates are capped by growth input; packets on independent ordinates buy at most their pole share;
- kernel, coupled and escape-form positivity and `D` are collided; zero-ordinate moments are Rosati pairings;
- every counting currency is the sign;
- one-variable positive constructions remove a quartet only against a real anchor; positive deformations keep the off-line divisor and are irreversible;
- no regulator of the prime place alone keeps positivity; coupling pays at most the partner's rank; covariant diagonal counterterms are scalar; the horizon divergence has unbounded rank on torsion orbits;
- local positivity at each prime does not sum; there is no common ladder over `ℤ`;
- uniform ceilings on terminals or Hecke defects are zero-free strips; zero-side reserves detect without bounding.

| Candidate | Present construction / exact boundary | (a) | (b) |
|---|---|---|---|
| **APF** adelic/Fourier | Countable Fourier data reconstruct the cycle; Fredholm trace receiver exact. | W1–W3 | Annihilation of the off-line component (B1.6). |
| **BSH** framed-mate curvature | Curvature detects line support; finite cutoffs trace-blind. | W1, W2 | Pre-divisor section with curvature sign (B1.6). |
| **CDC** constitutive dagger | Calibrated confluence ⇔ `Re s = 1/2`. | W1, W2 | A descending source potential (B1.6). |
| **DR** dyadic roots | Local cusp roots; finite monodromy; capped atlas. | W2, W3 | Global compatible roots (B2.1, B1.1). |
| **EGC** Euler/Gamma contour | Fixed-line correction; enclosed-pole cancellation. | W2–W4 | Outer contour sign (B1.6). |
| **EWJ** Euler–Wold jets | Exact finite jets. | W1, W2 | Norm exhaustion into a receiver (B1.6). |
| **FEL** free-energy contrast | BSY integral = off-line sum of `log\|ρ/(1−ρ)\|`. | W2 | Cofinal contrast equality (B1.7). |
| **HJ** pre-divisor reflection | Residual = SEC charge = two-grid HCF sign. | W1, W2 | Global stabilization weld (B1.6). |
| **IRK** inverse rotation kernel | Completed relation invertible off the line. | W1, W2 | Source lift with integral count (B1.6, B1.9). |
| **MSC** squarefree Hilbert source | Divisor-preserving `L²` source. | W2, W3 | Positive Sonin/Weil landing (B1.6). |
| **PCS** chronological carrier | Shift defect retained; norm gap. | W2 | Wall annihilation (B1.6). |
| **PTR** photonic ports | Finite lossless stacks real-rooted; prime-log stacks cannot converge to Ξ. | W2 | Prime-faithful nonlocal port (B1.6). |
| **RFHM** survival information | Full finite-support admission. | W2 | Phase-sensitive invariant (B1.6). |
| **SC** scattering completion | Wall recovery ⇔ wall vector = 0. | W2, W3 | Cross-fibre index (B1.6). |
| **SEC** time-one Fock | Fock boundedness ⇔ `Re ρ = 1/2`. | W1, W2 | Pre-divisor compactness (B1.6). |
| **W1C** Ising law convergence | Centred convergence suffices. | W2, W4 | Arithmetic couplings (B1.6). |
| **WBF** genealogy Gram | Completion ⇔ square-summable coefficients. | W2 | Arithmetic certificate stream (B1.6). |
| **PW-B** two-response action | Indexed by `XiZeroCopy`. | W2 | Pre-divisor form; zero-damping landing (B1.6, B1.2). |

The zero-indexed diagnostics of HJ, SEC, CDC, BSH, IRK and W1C read whether a zero's Hecke symbol is elliptic; they detect, they do not force. FEL's contrast, `Δ`, `M_f` and `𝓔` are depth capacities vanishing exactly on critical zeros; none has an arithmetic upper bound.

## 4. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| **BVI** rows and Vaughan | Minor arcs; all-modulus savings; bands ⇔ `Θ < 1`; width currency with VK decay (§1.14) [L]; single-scale prefix readings [S]. | W4, W16 | B2.1; B1.2 |
| **ACCE / ACCC** | Aperture flow; long-modulus decomposition; Kloosterman dispersion and omitted-class correction [L]. | W18 | B3.1, B3.4, B3.6 |
| **ADR / AOT** | Record minima; translated-zero escape rows; Mellin residues. | — | B3.2, B3.3, B3.12 |
| **ACS / Meyer** | §1.6, §1.12, §1.13. | W1 | B1.6, B1.8 |
| **ACP** | Correspondences, local types, counts, budgets, escape, terminals, the source field. | W10, W18 | B1.10, B3.16, B3.18, B3.19, B3.27 |
| **AES** electrostatics | §1.3; zero-ordinate counts; zero energy logarithmic; atomic stability law; gauge invisibility; gauge margin of the source [L/S]. | W9, W13, W21 | B1.13, B3.21, B3.24, B3.25 |
| **AIT** intersection theory | §1.4–§1.6: log-orders, different, cocycle, towers, local forms do not sum, square-root price, self-intersection dominates, spacing regulator, rotations, gauge-blind intersection, prime functional as finite intersection, polar part, tower-coordinate Hodge index, zero moments as Rosati pairings [L]; the base [S]. | W11, W12 | B3.26, B3.28, B3.29 |
| **RAPT** renormalized potential theory | Coupled survival law; arithmetic point matched to the archimedean place; covariance forces a scalar; covariant counterterm `log N + O(1)`; anomaly cost `½ log N`; horizon polar on uniform profiles, unbounded on torsion orbits [S]. | W11, W12 | B3.25, B3.26, B3.28 |
| **RBG** | Survival law; rank dichotomy; polar hyperplane; pole node; periodic germs; Ramanujan twins; dyadic amplification (soft); one-scale cap and terminal ceiling = strips; Harnack; cells; cell-holonomy defect; Kronecker dilution; lattice-cloud purchase bound [L/S]. | W12, W20 | B3.16, B3.21, B3.25 |
| **PL** | Polarization law; localizers; horizon; forcing half; `D` faithful, log-Sobolev; Gårding; negative index; selectivity battery. | W5, W18 | B1.11, B3.20 |
| **CDG** | `ξ` current; theta metrics; local detector; depth rigidity; forcing gap. | W8 | B3.20, B3.21 |
| **AE** | Effectivity calculus; heights; polar box; torsion potential; completion; Burgess; least non-residue; hyperelliptic calibration. | — | B1.9, B3.19, B3.23 |
| **BGG** | Gauge torus; successor holonomy; repulsion; deformation principle; quantization; ceiling transfer; `ζ^d` capacity. | W18 | B1.12, B3.16, B3.22 |
| **SP** | `181/500` and `23/40` separations; continuum-tower obstruction; escaped pairings; parity lobes; Jacobi–Hurwitz heights. | W5, W6 | B3.6, B3.16, B3.23 |
| **ACG** | Gauge invariance; a.e. laws; charged boundaries; gauge mass; coalescent surplus as gauge charge; sub-progression stabilizer inversion and `X^{1/4}` cell growth [S]. | W15, W20 | B1.2, B3.15 |
| **TTPC** | Census; `29/36` certificate; Ramanujan parity-twin limits, ultraviolet cancellation and infrared relocation; short-cycle positivity at lag `log 2` [L]. | W14 | B2.5, B2.7, B3.15 |
| **APD** | §1.13; Hecke states; Kakutani wall. | — | B1.6 |
| **MPG** | Boundary forcing; capacity; packets; height law. | W16 | — |
| **SBWF** | Collars; `κ = 1` class; `5d < 9κ`. | — | B3.13 |
| **AKT / AOG / ALDG / APT / BiScale / SAEI / SSA / THIM / Biarithmetic / HTG** | As in the frontier map; no change of boundary. | W4, W7, W18 | B1.4, B2.4, B3.3, B3.7–B3.11 |
| **Analytic inputs** | Guth–Maynard; 30/13 density; Selberg near-line density on `U^{99/100}`; Heath-Brown; dlVP, Littlewood, VK; smoothed Landau; discrete mean value at zero ordinates; the two-thirds certificate. | W7, W21 | B2.4, B2.8, B2.10 |

## 5. Not open tasks

- **Settled questions.**
  - What computes `D`, which norm it is, what its defect measures; every uniform bound on the defect or on terminals is a zero-free strip.
  - The electrostatic forms of RH and their quantization; the energy of one zero is between `1` (off-line) and `O(log γ)`.
  - Whether an off-line zero is visible at its own height (yes) and how often short prime polynomials align at zero ordinates (rarely: power-saving counts).
  - What zero-ordinate moments are: Rosati pairings.
  - Whether the prime place can be renormalized alone: no, under the Abel, spacing and horizon regulators; coupling pays at most the partner's rank; covariant diagonal counterterms are scalar; pole-node completion relocates the divergence to infinite node height.
  - Whether the archimedean place pays the prime place: yes at atomic resolution, with a rank-one pole counterterm, gauge blind.
  - Whether local positivity at each prime sums: no; summing in absolute value is the square-root threshold; there is no common ladder.
  - Which couplings are gauge charged; whether the source's gauge margin collapses (no: `2 log² p`, fixed by the smallest flipped prime).
  - The forcing gap; the first gauge-charged windows; escape classification; deformations of the coupled carrier; how far statistics reach; counting over `𝔽_q`; the width currency (§1.14).
- **Excluded mechanisms** (in addition to the [killed-routes catalogue](../rh-killed-routes.md)): collided positivity as Weil's sign; computed quantities offered as bounds on themselves; dyadic amplification as more than a rate (it is soft); the companion certificate spliced with the horizon; reserves, lenses and detectors as exclusion; the exterior law continued into the strip without an interior estimate; torsion-energy positivity or scalar-counterterm renormalization as Weil positivity; low-rank coupling of the Abel torsion block; fixed-rank subtraction of the horizon divergence; atomic-resolution positivity or the coefficient gauge margin offered as selective form positivity; square-class couplings as gauge selectors; alignment counts as exclusion of an individual zero; zero-ordinate moments as positivity input; uniform defect or terminal ceilings as weaker than a strip; budget currencies, heights or Farey sums as weaker inputs; raw continuum towers; completion at the arithmetic point; statistics as exclusion.
- **Substitutions that do not hold.** Computed for bounded; detected for excluded; counted for excluded; collided for Rosati; positive for equivariant; equivariant for positive; norm for sign; finite index for zero index; resonance for localization; twist for gauge charge; coefficient margin for form margin; gauge fixing for positivity; regularized limit for limit of positivity; scalar counterterm for renormalized positivity; covariance for survival; atomic resolution for the spacing scale; local Hodge index for global; exterior estimate for interior; amplification for rate improvement; uniform ceiling for non-uniform bound; finite window for all apertures; averages for individual zeros; nonnegative tests for the full cone; zero-indexed objects for pre-divisor constructions.
