# Hard mathematical obstacles: routes, candidates and supporting programmes

Status: 2026-10-27, corpus `3fd844e5f` with working tree. Scope: the 31 live routes, 17 standalone candidates, PW-B and the supporting programmes. Companions: [summary, next questions and new-field assessment](obstacles-summary.md), [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md).

## Evidence and classification

**Sources.** Route inventory: the [frontier map](../rh-current-frontier-map.md) and the [killed-routes catalogue](../rh-killed-routes.md). Statuses were researched with `scripts/formal_tools.py research` and by reading module docstrings and theorem statements in `formal/`; findings are recorded in `logs/review-2710-v5-research-log.md`. Nothing was compiled. Labels: `[L]` integrated source, `[S]` working or unintegrated source (as the frontier map marks it), `[P]` paper proof, `[R]` reading or model calculation of this review, not a theorem.

**Obstacle classes.**

- **(a) Just work.** Known mathematics suffices: finite certificates, certified computations, premise checks, transport of proved estimates, corollary assembly, sharp constants, imports of published theorems. IDs `W1`–`W25`, defined in the [summary](obstacles-summary.md#1-just-work). A just-work item may have an unknown outcome; what is known is the method.
- **(b) Open mathematics.** No known solution. Three tiers, defined in the [summary](obstacles-summary.md#2-open-mathematical-obstacles):
  - `B1.*`: RH-strength closing statements, each equivalent to RH or stronger;
  - `B2.*`: classical open problems weaker than RH;
  - `B3.*`: open problems isolated by this research, not known to be RH-equivalent.

**Notation.** `Δ = sup_ρ |Re ρ − 1/2|` (zero width), `Θ = 1/2 + Δ` (zero abscissa). A receiver bounded at rate `σ < 1/2` gives `Δ ≤ σ` (quasi-RH); RH is rate zero. `κ` is the pole order at `s = 1`, `d` the archimedean degree. For a zero `ρ` of multiplicity `m`: `ρ* = 1 − ρ̄`, depth `δ = Re ρ − 1/2`. `f̂(s) = ∫ f(u) e^{(s−1/2)u} du`.

- **Two forms.** `W` is Weil's form; `D(f) = Σ_ρ m_ρ |f̂(ρ)|²` the **collided form**; `Δ(f) = Σ_ρ (m_ρ/2)|f̂(ρ) − f̂(ρ*)|²` the **off-line defect**; `E_f(L) = D(T_L f) + D(T_{−L} f) − 2D(f)` the **Hecke defect**; `M_f = Σ_ρ m_ρ δ_ρ² |f̂(ρ)|²` the **moment of inertia**.
- **Electrostatics.** `E(p) = Σ_{q ≠ p} m_q/(p − q)` the field at a zero; `𝓔` the transverse energy of the distinct zeros, `𝓔_copy` that of the multiplicity copies; **damped source work** the arithmetic work of `Λ ⋆ Λ` against the divisor at damping `R`.
- **Torsion.** `I(m, n)` archimedean intersection of torsion orbits; `c(n) = I(n, n)/φ(n)`; `P(m, n) = Λ(n/m)(n/m)^{−1/2}` Weil's prime kernel; `K_q` the Kac–Murdock–Szegő tower matrix, `q = p^{−1/2}`; `Λ₂ = Λ log + Λ ⋆ Λ`.
- **Atomic families.** `f_x = Σ_{n ≤ N} x_n g(· − log n)` with a real `C²` bump `g` supported in `[0, w]`; spacing `δ_N = log(1 + 1/N)`; **overlap ratio** `K = w/δ_N ≍ wN`. `P_N(x) = Σ x_m x_n P(m, n)`; `ℓ(x) = Σ x_n n^{−1/2}` the polar functional; `M = arch − prime` the Markov form; `C(f) = ∫ f cosh(u/2)`, `S(f) = ∫ f sinh(u/2)`, so `Re W = M + 2C² − 2S²`. Constants: `c₁ = (32e^{5/2})^{−1}`, `C₀ = 2(log 4 + 4) + 1`, `c₀ = c₁ e^{−(C₀ + 2|θ′(0)|)}`.
- **Lorentzian.** A symmetric form is **hyperbolic** if it has at most one positive square, **Metzler** if its off-diagonal entries are nonnegative; for row sums `D = Q1 > 0` the **trickle-down inequality** is `(TD) Q[v] ≤ Σ_i (Qv)_i²/D_i`, weighted `(TD_π)` with a positive weight `π`.
- **Horizon classes.** For a prime `p`: classes `v_p(n) = j ≤ J`, densities `δ_j = (1 − 1/p)/p^j`, class polar functionals `ℓ_j`, local Euler constant `γ_p = γ + log p/(p − 1)`, tower deficit `d_p = √p log p/(p − 1) − γ`.

## 1. Facts that fix the present frontier

### 1.1 Two forms on the test space

| Form | Positive? | Hecke equivariant? | Computed by |
|---|---|---|---|
| Weil's form `W` | iff RH; finitely many negative directions at every aperture [L] | yes, for every zero configuration [L] | the explicit formula |
| Collided form `D` | yes; faithful; at each aperture the logarithmic Sobolev norm [L] | iff RH [L] | the `ξ` current and polynomially many integer theta values [L] |

- **Capacity identity** [L]. `Re W = D − Δ`; RH iff `W = D` iff `D` Hecke invariant iff one `T_L`, `L ≠ 0`, is a similitude of `D`.
- **Gårding is a finite-rank survival** [S]. `A ≥ 0` on a subspace of codimension `≤ k` iff `A` survives a positive counterterm of rank `≤ k`; the corpus Gårding bound says `W` is a renormalized positive form with finite-rank counterterm at each aperture; RH says the counterterm can be zero.
- **Moment of inertia** [L]. `4L²M_f ≤ E_f(L) ≤ 8(cosh L − 1)M_f`. Dyadic amplification is soft (valid for every nonnegative depth configuration) [L]. Every all-test, all-scale cap `E_f(L) ≤ D(f)(2cosh(2ϑL) − 2)` is the zero-free strip of width `ϑ` [S]. Integer-theta prefix readings: VK gives `o(n²)`; RH is subpolynomial readings on the dyadic schedule [L].
- **Reading [R].** What computes `D` and what its defect measures is answered; uniform bounds on the defect are strips; a non-strip bound must depend on the test or be averaged.

### 1.2 Local type, elliptic localizers and the forcing gap

At an off-line pair the local form is `2 Re(u v̄)` in `(f̂(ρ), f̂(ρ*))`, signature `(1, 1)`.

| Type | Action on the fibre | Correspondences | Positivity of a cyclic span forces |
|---|---|---|---|
| Hyperbolic | boost | Hecke operators, archimedean flow, gauge twists, at off-line pairs | isotropy |
| Elliptic | rotation or swap | Hecke on the line; resonant dilations; `σ_γ`; rotations of the circle | only `Re(u v̄) ≥ 0` |
| Unipotent | identity on polar parts | the successor | nothing |

- Resonance, `σ_γ` as the only reflection-compatible affine localizer, symmetric squares, sparse annihilators, rotations of the circle localizing in `ℚ/ℤ` [L].
- **Conductor horizon** [L]: twisted positivity once `C + (4 + ε)e^a + 2 ≤ log(1 + |γ|/8)`, source blind. **Forcing gap** [L]: the companion certificate needs `e^{2δa} > 768A log(|γ| + 3)`, disjoint from the horizon at every height.
- **Lorentzian reading of the local type** [S]. Hecke dilations `n ↦ pn` preserve every twin's coupled kernel and act on the pole plane by the boost `diag(p^{−1/2}, p^{1/2})`: conformal factor one. Power maps `n ↦ n^k`, `k ≥ 2`, and the successor are not conformal. Over `𝔽_q` Frobenius is a nonnegative conformal map with factor `q`. No map of the atoms available over `ℤ` is conformal with factor `≠ 1`.

### 1.3 Electrostatics and index descent of the zero divisor

- **Computed field** [L]: `L(Λ ⋆ Λ, s) = (ζ′/ζ)²`; Laurent coefficient = `2m` × transverse field. **Equilibrium, quantization** [L]: reflection-closed finite configurations are in equilibrium iff critical; RH iff every unit window has energy `< 2`.
- **Thresholds** [L/S]: RH iff every right-zero field `≤ 1`, iff `< √(2c log(|γ| + 4))`; `𝓔 < ∞` iff finitely many off-line zeros. **Closed quantum threshold** [S]: RH iff `𝓔 ≤ 2` iff `𝓔_copy ≤ 2` iff the damped source work is cofinally `≤ 2` (an off-line quartet carries energy `> 2`).
- **Energy of one zero** [L]: every off-line zero has `E(ρ) ≥ 1`; every zero `E(ρ) ≤ 16(C + log(|γ| + 4))`.
- **Index descent** [S]: the negative index `k` of any finite compact `C²` Weil Gram satisfies `k ≤ 𝓔 ≤ 𝓔_copy`, and `k > 0` forces `k < 𝓔`; damped source work eventually exceeds the whole index. `𝓔_copy < ∞` ⇔ finite off-line support ⇔ eventually bounded damped work ⇔ uniformly bounded index of the integer-log spline Grams. Finite-Gram descent: negative index survives entrywise approximation and cannot grow under rectangular pullback; arithmetic use needs convergence of every mixed entry. Above the zero-free height gap each reflected pair's work is monotone in the damping scale.
- **Terminals, rays, lens, Harnack** [L/S]: every right zero has a terminal within `C log γ` whose outward zero-free ray carries `Re(ζ′/ζ + Γ-part) ≥ m/h + m/(2a + h) + c·a·log γ`; terminal ceiling of depth `a` ⇔ strip of width `a` [S].
- **External field** [L]: for `σ > 1`, `Σ Λ(n) n^{−σ} cos(γ log n) ≤ Re(Γ-part)′ − m/(σ − β)` at a zero `β + iγ`; no interior counterpart.
- **Selberg's source and its gauge margin** [L]: `Λ₂ ≥ 0`, `L(Λ₂) = ζ″/ζ`; at a flipped prime `Λ₂(p) − ωΛ₂(p) = 2 log² p`, on every window — a coefficient margin.
- **Reading [R].** The zero side has an exact arithmetic target: an upper bound on damped source work below the quantum `2`. Detection, reserves, index bounds and quantization are all lower-side statements.

### 1.4 Torsion intersection and renormalization: the regulator decides

- **`Λ` is an intersection number** [L]: `I(m, mt) = φ(m)Λ(t)`, `Λ(n) = log #(𝒪_{ℚ(ζ_n)}/(ζ_n − 1))`. **Self-intersection dominates each tower** [L]. `P = Σ_p L_p`, each local tower form two-sided bounded, no global `ℓ²` ceiling; summing in absolute value costs `238√M`, the joint Schur bound is `log N + O(1)` [L].
- **Survival law** [L]: positivity passes to a regularized limit exactly on the null cone of the counterterm.

| Regulator | Counterterm | Survival | Hecke behaviour |
|---|---|---|---|
| Abel radius on torsion | identity | `{0}` [L] | anomaly cocycle `β(n, t)`, not a bounded coboundary [L] |
| Abel radius on the lattice germ | `𝟙𝟙ᵀ` | polar hyperplane [L] | — |
| Spacing radius `e^{−ε/n}` | scalar | `{0}`; limit indefinite on `{1, 2}` [L] | covariant up to tame ramification [L] |
| Horizon `n ≤ N`, uniform profiles | `ℓ(x)²` | polar hyperplane; finite part `−2γ` [S] | covariant [S] |
| Horizon, `p`-adic class profiles | tensor `Σ_j δ_j^{−1} ℓ_j(x)²` (torsion ⊗ polar) [S] | class-wise polar hyperplanes; finite part = tower form `−2γ_p + log p (K_q − 1)` [S] | exactly invariant under `[p]` (no anomaly) [S] |
| Horizon, exhaustion in `J` | unbounded rank | no fixed number of constraints removes the divergence [S] | — |

- **Coupling** [S]: a partner pays at most as many prime directions as its own counterterm rank; constant-mode archimedean coupling pays exactly the arithmetic point; pole-node completion relocates a full-rank divergence to infinite node height [L].
- **Covariance** [L]: a diagonal renormalization is Hecke covariant iff scalar (survival `{0}`); covariant counterterm `log N + O(1)`. **Torsion window** [S]: the minimal torsion counterterm lies in `[(3/2) log N − C₁, 2 log N + C₂]`; retaining self-intersections costs between `½ log N` and `log N` over the covariant one.
- **Sign of the tower finite part** [S]: in normalized class coordinates the horizon finite part enters Weil's form as `F_p(b) = 2γ_p|b|² + log p(|b|² − K_q(b))`; `F_p + c|·|² ≥ 0` at every depth iff `c ≥ 2d_p`. `d_2 > 0`; `d_p ≤ 0` for `p ≥ 2^16` (numerically for `p ≥ 47`). Large primes pay their own classes; small primes leave a deficit `2d_p`.
- **Polar matching reads the gauge density** [S]: the coefficient matching the prime divergence to the archimedean polar direction is the weighted density of unflipped minus flipped primes: `+1` for Euler and every finite-flip gauge, `−1` for Liouville.
- **Reading [R].** The horizon is Weil's own regulator and is the first one that is Hecke covariant with a nontrivial null cone on every finite class space; its finite part is local (tower forms with local Euler constants) and has a sign law decided by one number per prime. What is missing is uniformity under class and prime exhaustion on signed profiles, and payment of the small-prime deficits by the archimedean place and the pole. Divergences cannot separate `ζ` from finite-flip twins; only finite parts can.

### 1.5 The spacing scale and the overlap ratio

- **Self-energy of an atom is exactly logarithmic** [L]: `log(1/w)‖g‖² ≤ levyEnergy g ≤ (log(1/w) + C_E)‖g‖² + e^{1/2}K w‖g‖₁` — constant one, the constant of the covariant counterterm `log N`.
- **Tilted prime rows** [L]: with Schur weight `1 + n/N`, `P_N(x) ≤ Σ x_m²(log N + 2(log 4 + 4) − (m/4N) log m)`; the down-tower saving pays the archimedean cross-kernel row `(m/4N)(1 + log(N + 1))` at `w ≤ c₁/N`.
- **Stability law at the spacing scale** [L]: `M(f_x) ≥ (2θ′(0) + log(1/(wN)) − C₀)‖f_x‖²` at `w ≤ c₁δ_N`; `M ≥ 0` at `w ≤ c₀δ_N`, every `N`; `Re W + 2S² ≥ 0`; `Re W ≥ 0` on `|S| ≤ |C|`.
- **The law is universal** [L]: the same constants hold for every real twist `|ω(k)| ≤ 1`, multiplicative or not, and every real `C²` bump. The separated regime sees nothing of the coefficients beyond `|a(k)| ≤ Λ(k)`.
- **Diamagnetic inequality** [L]: `archForm f − twistedPrimeSum ω f ≥ M(|f|)` for every real compact `C²` `f` and every `|ω| ≤ 1`; on `|·|`-closed families `ζ` is the ground state of its gauge orbit. A form margin in `ζ`'s favour can come only from the pole term (the one anti-Markovian term) or from families not closed under `|·|` (signed bumps, overlapping atoms).
- **Sections pay the pole** [L]: for independent profiles `F = Σ G_n(· − log n)` of width `w ≤ c_full δ_N`, `Re W(F) ≥ ‖F‖²` with no pole constraint; restricted Riemann–Roch, ampleness and Hodge index hold on the whole section space. Gauge blind. The same holds for independent profiles on arbitrary intervals of width `δ < δ₀` with pairwise gaps `≥ s` and total span `≤ κ log(1/δ)`, `κ < 2` (below the pole scale) [S].
- **The gauge enters through non-ratio lags** [L]: at any width `primeSum f_x = Σ_k Λ(k) Σ_{m,n} x_m x_n (G(−log k − s_mn) + G(log k − s_mn))`; for completely multiplicative sign gauges the defect `ω(k) − ω(m)ω(n)` vanishes on ratio lags; below the spacing there are no non-ratio lags; for `N ≥ 3` a non-ratio pair lies within `4δ_N` of lag `log 2`. The infinite-sum identity retains two summability premises.
- **The atomic family is a Dirichlet polynomial** [L]: `h_{f_x} = h_g · D_x`; on-line zero summands are `m_ρ|h_g(γ_ρ)|²|D_x(γ_ρ)|² ≥ 0`. Below the spacing the zeros up to height `≍ 1/w` oversample the Dirichlet polynomials of length `N`; at the spacing they sample at the Nyquist rate; beyond it they undersample.
- **Unbounded overlap is RH** [L]: for every fixed width `w > 0`, RH iff all finite Weil Grams of the cubic splines `B_w(· − log n)` are positive semidefinite; the largest negative index is the number of distinct zeros right of the line.
- **Lévy-norm continuity** [S]: Weil's quadratic form splits exactly into `L²`, Lévy, prime and pole parts; `Q(f + d) − Q(f)` is bounded explicitly by `‖d‖₂`, the Lévy energy of `d` and `‖d‖₁` on a fixed window. The Lipschitz-perturbation lemma and the `N^{−θ}` synthesis (`TheCriticalExponent`) named in its docstring are not declared in the corpus.
- **Reading [R].** Positivity is unconditional exactly while the overlap ratio stays below `c₀`, and there it is universal; at unbounded overlap it is RH. The open regime is **bounded overlap**, `c₀ < K < ∞` — where non-ratio lags appear (from `K ≈ 4`), where the zeros sample the atomic Dirichlet polynomials at or below the Nyquist rate, and where the Nyquist rank bound of AOT says sampling stops being injective (`N ≍ T`, the square-root threshold read as a sampling threshold).

### 1.6 Arithmetic Lorentzian geometry

- **Hodge index = hyperbolicity** [S]: RH iff every finite Gram of the scaling surface satisfies `D²E² ≤ (D·E)²` whenever `D² > 0`. Any form with a hyperbolic plane becomes entrywise nonnegative in a shifted basis: nonnegativity informs only in a fixed basis.
- **Sums fail; trickle-down repairs them** [S]: hyperbolicity is not closed under sums; for a Metzler form with positive row sums and connected support, one positive square ⇔ `(TD)` ⇔ hyperbolic links exist; `(TD)` says `Q − QD^{−1}Q ≤ 0`, and negative semidefinite defects do sum. Quantitative `(TD)` with error `ε` plus a gap gives `Q ≤ μ₋(ε)D`.
- **Metzler dichotomy** [S]: if `Qπ ≤ 0` for some `π > 0` then `Q ≤ 0` — the stability regime, the shape of every unconditional atomic positivity; if `Qπ > 0` with connected support then hyperbolicity ⇔ `(TD_π)` — the trickle-down regime.
- **Calibration over `𝔽_q`** [S]: Bézout is the Metzler property (point counts `≥ 0`); every curve datum lies in the trickle-down regime; the golden datum (`q = 5`) is Metzler and connected but violates `(TD_π)`. The content of Weil's theorem is the trickle-down inequality.
- **The sign is a gauge fixing** [S]: the coupled atomic kernel `A + t χ̄(m)χ(n)P` (`N ≥ 6`, `t ≥ 2`) is entrywise nonnegative in some gauge iff `χ(p) = 1` for all `p ≤ N`; the archimedean kernel fixes the gauge along the successor; the Lorentzian locus of the gauge torus is the set of archimedean characters `n^{iτ}`. In the Euler gauge the archimedean phase on the successor edge is the successor connection of BGG.
- **Local factors** [S]: the prime kernel on a `p`-ladder `1, …, p⁵` has at least two positive squares (no local Lorentzian positivity); the archimedean jump form is a Laplacian (no positive square); the second elementary symmetric form of nonnegative local data is Lorentzian for every choice of data, so the Euler-product closure is blind (Beurling systems and fake curves pass); its identification with the Hessian of `∏⟨L_p, y⟩` is being formalized.
- **Repairs that change the form** [S]: the odd Frobenius Gram is the minimal-rank positive repair (rank = number of distinct outer eigenvalues), preserving pole couplings; polar gluing gives `reserve(ΣQ_i) = Σ reserve − V` (dispersion of normalized polar rows) and subtracting `V` constructs a hyperbolic form.
- **Turán layer** [S]: every homogenized Jensen polynomial of `ξ` at the centre (ordinary coefficients) is Lorentzian; strictly weaker than real-rootedness at degree `≥ 3`.
- **Reading [R].** In this language the atomic positivity proved by SSHA is the stability regime, and the overlap regime is the trickle-down regime. The Lorentzian sign hypothesis (Metzler) holds only at the Euler gauge: selectivity is built into the hypothesis rather than extracted from a margin. Over `ℤ` the missing pieces are a conformal correspondence (Frobenius) and arithmetic trickle-down links.

### 1.7 Weil's argument over `ℤ`, layer by layer

| Layer | Over `𝔽_q` | Over `ℤ` | Forces the sign? |
|---|---|---|---|
| L1 Identities | Lefschetz, adjunction | exact | no (golden datum) |
| L2 Theorem of the square | graph map quadratic | free for normalized graphs | no |
| L3 Budget | `δ(Δ, Δ) = 2g` | free | no |
| L4 Kernel counts / Bézout | `#ker ≥ 0` = Metzler | collided; atomic kernel Metzler only in the Euler gauge [S] | collided only |
| L5 Rosati positivity / Hodge | polarization | `⇔` RH; `⇔` hyperbolicity of scaling-surface Grams | missing |
| L5′ Counting origin | RR on `C × C`; Stepanov | each counting currency is RH | each is RH |
| L5″ Diagonal | `2 − 2g`, finite | archimedean self-energy pays the prime intersection and the pole up to overlap ratio `c₀` [L]; RH at unbounded overlap [L] | missing at bounded overlap |
| L5‴ Local–global | trickle-down on one Frobenius ladder | local ladders not Lorentzian; local Hodge index at each prime; horizon finite parts local with deficit `2d_p` at small `p` | missing: trickle-down links |
| L5⁗ Symmetry | Frobenius conformal, factor `q` | Hecke isometries; power maps and successor not conformal | missing: a conformal correspondence |
| L6 Amplification | fixed tensor loss | `⇔` RH; dyadic amplification soft | missing |

**Calibration over `𝔽_q`** [L]: odd-degree hyperelliptic RH by counting. **Completion law** [L]: `|τ|² = q`; Burgess; least non-residue; the arithmetic point has no period.

### 1.8 Counting and budgets

- Section counts, effectivity, naive and convex heights, fixed tensor loss, horizon torsion, the one-sided count `ψ(x) − x ≤ C√x log²x`, the Farey sum: each RH [L]. Nyquist rank bound: readings cannot annihilate more tests than their degrees of freedom allow; injective below the diagonal `N ≪ T` [L].
- Prime-error linear budget ⇔ RH; Abel slope at the genus ⇔ RH + simple zeros; Mertens budget ⇒ RH + simple + summable residues [L]; over `𝔽_q` slopes `Σ mult(β)²` [L].

### 1.9 The gauge principle

- **Orbits** [L]: multiplicative data determine a source up to its gauge orbit; the Möbius half-power law holds Haar-a.e., fails at Liouville, is RH at the gauge point `0`.
- **Blind** [L/S]: square-class couplings; the finite intersection; the separated regime of the Markov form for every bounded twist (universal law); `|·|`-closed families (`ζ` the ground state); divergences of the horizon renormalization (polar matching `+1` for every finite flip); the Euler-product closure.
- **Charged** [L/S]: successor couplings; dyadic cells (defect `≥ 2·#charged cells`, `≥ X^{1/4}` for every gauge flipping `2`; Liouville `≥ 2J` on `[1, 8J⁴]`); the archimedean kernel on successor edges (Lorentzian sign only at Euler); non-ratio prime lags at overlap; finite parts (source margin `2 log² p`; tower finite parts); the pole term.
- **First windows** [L]: at `181/500` and `23/40` the Liouville and `{2}`-flipped twins fail on witnesses where `ζ` is positive, Liouville permanently from `23/40` on; the full `ζ` floor at `23/40` is uncertified.
- **Reading [R].** Every gauge-blind statement is now classified by a structural reason; every remaining selective input lives in a finite part, a non-ratio lag, the pole term or the archimedean successor phase.

### 1.10 Positive systems, deformations, escape

`CompletedPositiveSystem 1 d = ℝ^× · ζ`; pole order pays inserted zeros; anchored quartet `⇒ κ ≥ 3`; independent-ordinate packets buy their pole share, lattice clouds a finite multiple [L/S]; positive deformations detect zero-free ordinates and are irreversible [S]. RH iff admission at every damping iff positive gauge mass of every escape state; escape classifies, it does not exclude [L].

### 1.11 Positivity: windows, averages, statistics, zero ordinates

- Floors `‖f‖²/5000` (full) and `‖f‖²/1000` (odd) through `181/500`; short-cycle positivity at lag `log 2` [L]. Averaged positivity on `Γ^{99/100} ≤ H ≤ Γ/8`; positive proportion of heights; census `≥ 4/5` of ordinates critical, `≥ 3/4` of copies within `4/log T` [L].
- **Critical-line proportion** [L]: simple critical zeros `≥ HD(1) + 10^{−8}` (`> 67.250071%`), distinct zeros `≥ GD(1) + ½·10^{−8}`, by disjoint-pair Schur slack and the non-lattice floor of the Montgomery–Taylor cosine kernel.
- **Alignment counts** [L]: a prime polynomial of length `(log T)^C` reaches `η log T` at `T^{1 − 1/C + o(1)}` zero ordinates; no implication "off-line ⇒ aligned". **Zero moments are Rosati pairings** [L].

### 1.12 Realization and duality; the width currency

- Maximal sharp-stable positive Meyer ideal = off-line-blind ideal; coupled point-stable carriers isotropic; positive self-dual measures with a gap are Dirac combs; Hecke states positive definite iff `s ≥ 1/2` [L].
- **Width currency** [L]: for `0 < θ ≤ 1/2` escaped Möbius `θ`-decay ⇔ receiver rate `≤ 1/2 − θ` ⇔ `Θ ≤ 1 − θ` ⇔ all-test Hecke strip cap ⇔ dyadic rate `1 − 2θ` ⇔ `Re ξ′/ξ ≥ 0` on `Re s > 1 − θ` ⇔ prefix-reading rate; unconditionally only VK rates.

**Every unconditional positivity in the corpus is one of:** invariant (blind, half-blind, isotropic); averaged or statistical; non-localizing; on nonnegative tests; collided; twisted below the conductor horizon; a finite-window certificate; local at one prime; carried by a counterterm whose survival cone is `{0}`, a hyperplane or the arithmetic point; coefficient positivity of a source; a zero-side reserve; **separated: overlap ratio `≤ c₀`, universal for every bounded twist, including the full form on independent-profile sections**; a constructed (repaired or glued) form.

### 1.13 Thresholds where proved positivity stops

| Threshold | Proved below | Open at or beyond |
|---|---|---|
| Overlap ratio `K = w/δ_N` | `M ≥ 0`, `Re W + 2S² ≥ 0` at `K ≤ c₀`; `Re W ≥ ‖F‖²` on sections at `K ≤ c_full`; universal | `c₀ < K < ∞`: non-ratio lags from `K ≈ 4`; Nyquist undersampling; `K = ∞` is RH |
| Metzler stability (`Qπ ≤ 0`) | atom block negative semidefinite | trickle-down regime (`Qπ > 0`): `(TD_π)` |
| Conductor horizon `e^a ≲ log γ/4` | twisted positivity, source blind | odd-sector sign; forcing needs `e^{2δa} > 768A log γ` |
| Square-root threshold / Nyquist diagonal `N ≍ T` | Landau–Gonek moments; injective sampling; local indices summed at `√M` | Rosati products beyond; sampling with hiding |
| Tower deficit `d_p ≤ 0` | prime finite part pays its own classes for `p ≥ 2^16` (numerically `p ≥ 47`) | small primes: deficit `2d_p` |
| Half damping `ε = 1/2` | all receivers bounded | signed sub-half control |
| Apertures `181/500`, `23/40` | certified floors and separations | all apertures |
| Vinogradov–Korobov | sub-power savings | any power saving |
| Detector length `(log T)^C` | power-saving alignment counts | an individual zero |
| Quantum `2` of source work | index `<` energy; detection of every index | an upper bound |

## 2. The 31 routes

Each entry: status; (a) just work; (b) open; walls ([walls ledger](walls-ledger.md)).

### WL — Weil lag function
**Status.** Spline, lag, deficit and critical-energy receivers read `Δ`; RH ⇔ critical energy bounded ⇔ `ψ(x) − x ≤ C√x log²x` eventually ⇔ horizon torsion ⇔ the Farey sum ⇔ a linear prime-error budget; RH + simple ⇔ Abel slope at the genus.
**(a)** Averaged bounded-energy statement (W18); windows `Γ^{1/2+ε}` (W7); finite budgets (W2); census transport (W14).
**(b)** Signed lag cancellation at every slack (B1.1); an actual budget (B1.10); selection (B1.4); quasi-RH (B2.1).
**Walls:** 1.0, 1.1, 1.15, 1.19, 3.14.

### RW — Restricted Weil ground energy
**Status.** RH ⇔ `μ(A) > 0` for all `A`; flow never stalls; cumulative relaxation criterion; ground rate = polar rate; Gårding as a finite-rank survival; floor `1/5000` through `181/500`.
**(a)** Certified floors past `181/500` (W5); rate dictionary (W18); transport of census, moment-of-inertia and spacing-scale laws (W4).
**(b)** Zero negative index at every aperture (B1.3); signed shell flux (B3.4); `polarRate = Δ` for clustering zeros (B3.1); selection (B1.4).
**Walls:** 1.3, 1.11, 1.13, 3.2, 3.14.

### FU — CCM-FU signed prime scheduling
**Status.** Both one-sided bounds of the completed Möbius–divisor Abel moment are RH-equivalent; narrow-window negative prime channel, not on dyadic windows [S].
**(a)** Finite schedules (W2); wide-window premises (W3).
**(b)** Complete-history signed cancellation (B1.1).
**Walls:** 1.1, 1.6, 3.2, 3.4.

### RP — Route-P / SP-E history floor
**Status.** Eventual matched-quantile history floor ⇔ RH; low-LCM payment proved.
**(a)** Finite floors (W2); low-LCM transport (W4).
**(b)** Full-history floor with high-LCM pairs, moving core and singular transport (B1.1).
**Walls:** 1.1, 1.8, 3.6.

### PA — Prime–archimedean source passivity
**Status.** Current, Bernstein-mismatch and signed-moment receivers RH-equivalent; each fixed Hausdorff order positive beyond its shift threshold.
**(a)** Explicit fixed-order thresholds (W5); finite blocks (W2).
**(b)** Order-uniform thresholds (B3.10); all-order passivity (B1.5).
**Walls:** 1.5, 1.6, 14.1.

### MC — Möbius cancellation at half power
**Status.** `M(x) = Ω±(√x)`; RH ⇔ `M(N) = O(N^{1/2+δ})` ∀`δ`; Mertens budget ⇒ RH + simple + summable residues; width currency with VK-rate escaped decay uniform in `N, a, b`; prefix readings; Burgess and least non-residue; Kloosterman dispersion and omitted-class correction.
**(a)** Mertens converse under RH and `J_{−1}(T) ≪ T` (W18); finite budgets (W2); VK as a growth-to-forcing instance (W16).
**(b)** Square-root cancellation at `0` (B1.1); an actual budget (B1.10); quasi-RH, e.g. `Θ ≤ 7/8` (B2.1); power-saving sign correlations (B2.6); a gauge-charged statistic at `0` (B3.15); growing-packet compensation (B3.6).
**Walls:** 1.0, 1.1, 1.12, 1.18, 1.19, 1.20, 3.10.

### TT — Theta tail and heat–Cassini currents
**Status.** Directed Wold receiver; RH ⇔ the bound at every `t ∈ (0, 1/2)`; restricted current signs.
**(a)** Finite covariances (W2); ACT/OWU transport (W4).
**(b)** Complete odd Weil positivity (B1.3).
**Walls:** 1.3, 1.6, 3.4.

### LA — Line anchor
**Status.** RH ⇔ all-height head coefficient positivity at fixed `R² ≥ 1/2`; heat repairs high heads; `0 ≤ Λ < 1/8` in corpus normalization (standard `< 1/2`) [L]; Taylor coefficients of `ξ(1/2 + x)` form a Turán sequence [L]; every homogenized Jensen polynomial at the centre is Lorentzian [S] — the log-concavity layer, not real-rootedness.
**(a)** Residual region (W18); finite heads (W2); import of the Polymath bound (W18); the factorial-normalized Newton inequalities at fixed degree from existing Turán data (W2).
**(b)** Zero-heat sign on the residual region (B1.5, B3.7); all-degree real-rootedness (B1.5); de Bruijn–Newman beyond the literature (B2.9).
**Walls:** 1.2, 1.6, 1.14.

### TG — Topological sub-unit gate
**Status.** Anchored cubic trace = winding; an integral nonnegative residual below one vanishes.
**(a)** Disc-wise traces (W2); Gaussian covariance transport (W4).
**(b)** Residual sign and sub-unit bound for a pre-divisor source (B1.6).
**Walls:** 1.2, 14.3, 14.8.

### HF — Positive Hodge form on arithmetic cohomology
**Status.** `D_idx` even when finite, RH ⇔ `D_idx < 2`; the two forms and the moment of inertia (§1.1); electrostatics, closed quantum threshold and index descent (§1.3); the regulator table, horizon tensor counterterm and tower finite-part sign law (§1.4); spacing-scale stability, universality, diamagnetism and unbounded overlap (§1.5); hyperbolicity, trickle-down and gauge fixing (§1.6); zero moments as Rosati pairings; alignment counts.
**(a)** Copy versus distinct energy (W13); quadrature of readings (W8); overlap certificates (W9); counterterm constants (W11); overlap bookkeeping (W12); Lévy synthesis (W22); horizon class asymptotics (W23); local trickle-down data (W24); small-prime deficit table (W25); working sources (W19).
**(b)** Zero negative index (B1.3); `D_idx < 2` (B1.7); counting forms (B1.9); equivariance of `D` (B1.11); field, energy and source-work forms (B1.13); finite off-line index (B2.2); compatible families (B3.8); a non-uniform bound on `M_f` (B3.21); alignment (B3.24); bounded overlap (B3.26); horizon finite part (B3.28); conformal symmetry and base (B3.29); trickle-down for `ζ` (B3.30).
**Walls:** 1.3, 1.4, 1.16, 1.17, 1.21, 3.13, 3.20, 3.22, 3.23, 3.25, 3.26, 14.2, 14.18, 14.21, 14.24, 14.26–14.33.

### CHMD — Causal hyperbolic–modular duality
**Status.** Odd energy nonnegative iff no odd bound state above `1/2`; completion, cuts, domains and nodal convergence proved.
**(a)** Domain premises (W3); RW/SZ transport (W4).
**(b)** The nodal inequality (B1.3).
**Walls:** 1.3, 3.3, 3.4.

### TH — Theta moment positivity
**Status.** All-rank strict positivity on the orthant at small time; fixed-rank coercivity.
**(a)** Explicit fixed-rank regions (W5).
**(b)** Signed coefficients at all degrees under one heat time (B1.5); decoupling rank from time (B3.10).
**Walls:** 1.6, 3.11.

### RN — Theta renewal and singular comparison
**Status.** A compact cone-positive renewal operator realizes the denominator through `det₂`; cone positivity does not confine resonances.
**(a)** Finite packets (W2); `det₂` transport (W4).
**(b)** Boundary-current orientation for the actual source (B1.6).
**Walls:** 1.2, 14.1, 14.3.

### WD — Ward orientation and horizontal collision
**Status.** Global cap vanishes iff RH; Hermite barrier, optimal heat and large-height repair formalized.
**(a)** Residual region (W18); finite heads (W2).
**(b)** Cap vanishing (B1.6); residual heat sign (B1.5).
**Walls:** 1.2, 1.14, 3.8.

### LI — Paired Li and prime–Gamma balances
**Status.** RH ⇔ subexponential lower floors at every positive rate; reciprocal-depth rate `≤ 1/431`.
**(a)** Finite floors (W2); constants (W5).
**(b)** The subexponential floor (B1.7).
**Walls:** 1.5, 3.8.

### SZ — Suzuki screw and shifted-kernel limits
**Status.** Compact-`L²` first variation = extended Weil energy; RH ⇔ nonnegative first variation on RH-complete tent families.
**(a)** Limit-family premises (W3); RW transport (W4).
**(b)** The first-variation sign (B1.3).
**Walls:** 1.3, 3.3, 3.6.

### PM — Physical-model Haar approximation (FZZ-P)
**Status.** RH ⇔ admission at every damping ⇔ positive gauge mass; energy-rate law; Abel atoms; escape classified.
**(a)** Cofactor premises (W3); transport of VK-rate decay and Kloosterman dispersion (W4).
**(b)** Signed small-damping energy (B1.2); infinite-height escape (B3.2); inverse coercivity (B3.3); sub-half control (B3.9); paid ideal on escape (B3.12).
**Walls:** 1.8–1.10, 3.7, 3.12, 3.15.

### JAS — Joint ancestry
**Status.** Positive level-one budget ⇔ half-plane bound; unconditional positivity reaches a logarithmic prime budget.
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
**Status.** Line-centred Newton discs covering every zero ⇔ RH; margin subharmonic.
**(a)** Finite covers (W2).
**(b)** Covering discs with nonnegative margin (B1.5).
**Walls:** 1.2, 3.2, 14.3.

### BAG — Deterministic zeta self-return
**Status.** Strong, local and cutoff-uniform recurrence each RH-equivalent; recurrence exactly at non-zeros.
**(a)** Threshold-law transport (W4).
**(b)** Returns near possible zeros (B1.7).
**Walls:** 1.2, 3.2.

### EWU — Even pole-weight uniqueness
**Status.** Blind minima nonnegative at every aperture ⇔ RH; source selection; floor `1/5000` through `181/500`, shared by every weight with `w(2) = log 2`.
**(a)** Certified floors (W5); margin table (W6).
**(b)** Low and mixed modes (B1.3); gauge form margin (B3.16).
**Walls:** 1.3, 1.4, 3.3.

### GTA — Transverse Schur charge
**Status.** Uniform quartic Schur decay RH-equivalent; an off-line zero forces a late positive charge floor.
**(a)** Finite truncations (W2).
**(b)** Rank-uniform decay (B1.5).
**Walls:** 1.6, 3.2.

### OWU — Odd Weil-weight uniqueness
**Status.** Odd positivity RH-equivalent; at `181/500` and `23/40` the Liouville and atom-2 twins fail where `ζ` is positive, permanently from `23/40` on; short-cycle positivity at lag `log 2`; companion certificate and conductor horizon disjoint; zero-side reserve and exterior law at the same ordinates; alignment counts.
**(a)** Full floor at `23/40`, margin tables (W5, W6); interior reading of the reserve (W10); exceptional-set accounting (W21); twins at overlap (W9).
**(b)** Odd Weil positivity (B1.3); gauge form margin (B3.16); odd-sector sign beyond the horizon (B3.20); alignment (B3.24); bounded overlap (B3.26); terminal control off a sparse set (B3.27).
**Walls:** 1.3, 1.18, 1.21, 3.4, 3.19, 3.26.

### PBM — Regularized prime/log-ζ abscissa
**Status.** Half-plane bound at `α` ⇔ convergence on `Re s > 1/2 + α`; RH is `α = 0`.
**(a)** Width-currency transport (W4).
**(b)** Quasi-RH (B2.1); critical cancellation (B1.1).
**Walls:** 1.0, 1.1.

### RB — Robin/Nicolas
**Status.** Eventual Robin ⇔ Robin on colossally abundant numbers; counterexamples need growing lcm cores.
**(a)** Finite verifications (W2).
**(b)** The eventual Robin tail (B1.7).
**Walls:** 1.1, 1.6.

### SRT — Prime-side one-parameter lag localization
**Status.** One fixed-width late-lag family decides RH; smooth detector; one- and two-prime Lefschetz receivers are the strip; detector = odd sector of `σ_γ`; conductor horizon; forcing gap; exterior law; alignment counts; short-cycle positivity. For every fixed `w > 0` the integer-log spline Grams have negative index zero iff RH and their maximal index counts the distinct right zeros [L]; a uniform finite index bound ⇔ finite off-line support [S].
**(a)** Rate dictionary (W18); interior reading of the reserve (W10); exceptional-set accounting (W21); windows (W7); overlap certificates (W9).
**(b)** Selection (B1.4); critical cancellation (B1.1); Weil positivity (B1.3); counting forms (B1.9); near-coincidence beyond `½ log Γ` (B3.14); odd-sector sign beyond the horizon (B3.20); alignment (B3.24); bounded overlap (B3.26); terminal control off a sparse set (B3.27).
**Walls:** 1.17, 1.21, 3.1, 3.2, 3.14, 3.19, 3.26.

### ACT — Arithmetic criticality / single-shift variation
**Status.** One fixed shift against all even compact profiles decides RH; light-cone kernel positive; sub-unit collar paid for `log d ≤ a − R`.
**(a)** Collar constants (W5); TT/OWU transport (W4).
**(b)** The uniform all-profile collar (B1.3).
**Walls:** 1.3, 3.1, 3.4.

### AIP — Arithmetic incidence positivity
**Status.** Allocation for all tests ⇔ RH; shared-budget descent; joint `2, 3` payment at `23/40`; raw continuum towers negative `≥ c e^A`. Spacing scale (§1.5): Markov stability at `c₀δ_N` for every bounded twist; diamagnetism; non-ratio lags; tilted rows; full pole payment on independent-profile sections. Horizon (§1.4): tensor counterterm, covariance, tower finite part and sign law. Lorentzian (§1.6): the atomic kernel is Metzler only in the Euler gauge; prime ladders not Lorentzian; finite-product closure nonselective.
**(a)** Certified joint payments at larger apertures (W5); overlap certificates (W9); overlap bookkeeping (W12); Lévy synthesis (W22); horizon asymptotics (W23); local trickle-down data (W24); small-prime deficits (W25).
**(b)** Weil positivity (B1.3); prime-weighted shared budget for the pole-neutralized continuum form (B3.6); gauge form margin (B3.16); bounded overlap (B3.26); horizon finite part (B3.28); trickle-down for `ζ` (B3.30).
**Walls:** 1.3, 1.18, 3.4, 3.21, 3.23, 3.25, 3.26, 14.31, 14.32.

### ACS — Arithmetic Castelnuovo–Severi effectivity
**Status.**
- Source RR; Meyer RR + Bézout; maximal blind ideal; isotropy; Lefschetz receivers; faithful degree needs RH + simple zeros; counting and deformations; Selberg's source with gauge margin `2 log² p`.
- Arithmetic sections [L]: on independent-profile sections at a fixed fraction of the spacing, `Re W ≥ ‖F‖²` with no pole constraint; restricted Riemann–Roch, ampleness and Hodge index on the whole section space. Width shrinks with `N`; no source-complete exhaustion.
- Scaling-surface Hodge index ⇔ hyperbolicity ⇔ RH; Frobenius calibration and half-defect repair [S].
**(a)** Selectivity battery (W1); ceilings and quantization in ACS coordinates (W18); contraction (W17); counterterm constants (W11); working sources (W19); section exhaustion bookkeeping with Lévy continuity (W22).
**(b)** Forcing for a realization (B1.6); faithful branch (B1.8); counting forms (B1.9); equivariance of `D` (B1.11); ceilings and chirality (B1.12); field forms (B1.13); collar equality (B3.13); `Λ ⋆ Λ` form positivity (B3.17); full coupled class (B3.22); selective polarization (B3.23); bounded overlap (B3.26); horizon finite part (B3.28); conformal symmetry and base (B3.29); trickle-down for `ζ` (B3.30); `3/4` (B2.5).
**Walls:** 1.3, 1.15–1.18, 1.21, 3.8, 3.14, 3.18, 3.23–3.26, 14.4, 14.8, 14.10–14.33.

## 3. The 17 candidates and PW-B

A candidate lacks an independent source construction or landing; each faces B1.6. These theorems constrain every candidate:

- single-channel sharp-stable positivity certifies only blindness; coupled point-stable positivity only isotropy; non-localizing positivity holds for every prime weight;
- multiplicative correspondences act hyperbolically at off-line pairs; `σ_γ` is the only reflection-compatible affine localizer; rotations of the circle cannot localize zeros; no correspondence over `ℤ` is conformal with factor `≠ 1`;
- positivity on nonnegative tests is shared by dominated twins; square-class couplings, the finite intersection, the separated regime and `|·|`-closed families are gauge blind;
- finite multiplicative certificates are capped by growth input; packets on independent ordinates buy at most their pole share;
- kernel, coupled and escape-form positivity and `D` are collided; zero-ordinate moments are Rosati pairings;
- every counting currency is the sign; Euler-product closures are Lorentzian for every nonnegative local datum;
- positive deformations keep the off-line divisor and are irreversible;
- no regulator of the prime place alone keeps positivity on the full space; the horizon keeps it only on class-wise polar-neutral profiles, with unbounded rank;
- uniform ceilings on terminals or Hecke defects are zero-free strips; zero-side reserves detect without bounding; finite Weil indices are bounded by energy, not by arithmetic.

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

The zero-indexed diagnostics of HJ, SEC, CDC, BSH, IRK and W1C read whether a zero's Hecke symbol is elliptic; they detect, they do not force. FEL's contrast, `Δ`, `M_f`, `𝓔` and the damped source work are depth capacities vanishing exactly on critical zeros; none has an arithmetic upper bound.

## 4. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| **SSHA** spacing-scale harmonic analysis | Exact self-energy; tilted rows; stability at `c₀δ_N`; universal law; diamagnetism; non-ratio lags; Dirichlet-polynomial dictionary; unbounded overlap = RH [L]; Lévy continuity [S]. | W9, W12, W22 | B3.16, B3.26 |
| **ALG** arithmetic Lorentzian geometry | Hyperbolicity; trickle-down; Metzler dichotomy; `𝔽_q` calibration; gauge fixing; successor gauge field; local factors; conformality; half-defect repair; polar gluing; Turán layer [S]. | W1, W24 | B3.29, B3.30 |
| **AID** arithmetic index descent | Index `≤ 𝓔 ≤ 𝓔_copy`; index `< 𝓔`; closed quantum threshold `2`; finite stratum; finite-Gram descent; singular refinement [S]. | W13, W19 | B1.13, B2.2 |
| **RAPT** renormalized potential theory | Coupled survival; arithmetic point; covariance; torsion window; Gårding as survival; horizon polar, tensor and covariant counterterms; finite parts `−2γ` and tower forms; sign law `d_p`; polar matching [L/S]. | W11, W23, W25 | B3.28 |
| **IGP** incommensurable Gabor pinching | Disjoint-pair Schur slack; Montgomery–Taylor non-lattice floor; simple critical proportion `> 67.250071%` [L]. | W14 | B2.5 |
| **AES** electrostatics | §1.3; zero-ordinate counts; energy of a zero; atomic stability; gauge at atomic resolution; gauge margin of the source [L/S]. | W13, W21 | B1.13, B3.21, B3.24 |
| **AIT** intersection theory | Log-orders, cocycle, towers, local forms do not sum, square-root price, self-intersection dominance, spacing regulator, rotations, finite intersection, polar part, tower coordinates, zero moments; the base [S]. | W11 | B3.29 |
| **RBG** | Survival law; rank dichotomy; Ramanujan twins; dyadic amplification; strips; Harnack; cells and Liouville fourth-root growth; Kronecker dilution; lattice clouds [L/S]. | W20 | B3.16, B3.21 |
| **PL / CDG** | Polarization law; localizers; horizon; forcing half; `D` faithful, log-Sobolev; `ξ` current; theta metrics; forcing gap [L]. | W5, W8 | B1.11, B3.20 |
| **AE / AOT** | Effectivity; heights; polar box; completion; Burgess; hyperelliptic calibration; Nyquist rank bounds [L]. | — | B1.9, B3.19, B3.23 |
| **BGG / SP / ACG** | Gauge torus; successor holonomy; repulsion; deformation principle; quantization; `181/500`, `23/40` separations; cell growth [L]. | W5, W6, W20 | B1.12, B3.15, B3.16, B3.22 |
| **BVI / ACCE / ADR / ACP** | Width currency; VK decay; prefix readings; Kloosterman dispersion; escape; budgets; terminals [L]. | W4, W16, W18 | B1.2, B1.10, B2.1, B3.1–B3.6, B3.12 |
| **TTPC / APD / MPG / SBWF** | Census; Hecke states; boundary forcing; collars [L]. | W14, W16 | B2.5, B2.7, B3.13 |
| **AKT / AOG / ALDG / APT / BiScale / SAEI / SSA / THIM / Biarithmetic / HTG** | As in the frontier map. | W4, W7, W18 | B1.4, B2.4, B3.3, B3.7–B3.11 |
| **Analytic inputs** | Guth–Maynard; 30/13 density; Selberg near-line density; Heath-Brown; VK; discrete mean value at zero ordinates. | W7, W21 | B2.4, B2.8, B2.10 |

## 5. Not open tasks

- **Settled questions.**
  - What computes `D`, which norm it is, what its defect measures; uniform caps on the defect or on terminals are strips.
  - The electrostatic forms of RH, their quantization and the closed threshold `2` for energy and source work; finite indices are paid by energy.
  - Whether the archimedean place pays the prime place: yes, up to overlap ratio `c₀`, with constant one on both sides, for every bounded twist; the full form including the pole is paid on independent-profile sections.
  - Whether the separated regime can select `ζ`: no (universal law); whether `|·|`-closed families can: no (diamagnetism).
  - Whether positivity at fixed width is weaker than RH: no (unbounded overlap is RH).
  - Whether the horizon regulator is covariant with a nontrivial null cone: yes on each finite class space; what its finite part is (tower forms with local Euler constants) and when it is nonnegative (`d_p ≤ 0`).
  - Whether divergences can separate `ζ` from finite-flip twins: no (polar matching).
  - Whether local Lorentzian structure exists at a prime: no; whether the Euler-product closure selects: no; whether Hecke, power or successor maps are conformal: no.
  - Whether local positivity at each prime sums: no; the forcing gap; escape classification; deformations; counting over `𝔽_q`; the width currency; the census and alignment frequencies.
- **Excluded mechanisms** (in addition to the [killed-routes catalogue](../rh-killed-routes.md)): collided positivity as Weil's sign; computed quantities as bounds on themselves; dyadic amplification as more than a rate; the companion certificate spliced with the horizon; reserves, lenses, detectors and index bounds as exclusion; torsion-energy positivity or scalar-counterterm renormalization as Weil positivity; low-rank coupling of the Abel torsion block; fixed-rank subtraction of the horizon divergence; separated-regime, `|·|`-closed or section positivity as selective; polar matching as a selector; separate Lorentzian blocks or a nef shift as a Hodge sign; repaired or glued forms as the actual form; Hecke, power or successor maps as Frobenius; the Euler-product closure as a selector; alignment counts as exclusion; zero moments as positivity input; budgets, heights or Farey sums as weaker inputs; statistics as exclusion.
- **Substitutions that do not hold.** Computed for bounded; detected for excluded; counted for excluded; collided for Rosati; positive for equivariant; equivariant for positive; norm for sign; finite index for zero index; index for energy bound; resonance for localization; twist for gauge charge; coefficient margin for form margin; gauge fixing for positivity; Metzler for hyperbolic; constructed form for actual form; regularized limit for limit of positivity; scalar counterterm for renormalized positivity; covariance for survival; separated regime for overlap; local Hodge index for global; isometry for conformality; exterior estimate for interior; uniform ceiling for non-uniform bound; finite window for all apertures; averages for individual zeros; nonnegative tests for the full cone; zero-indexed objects for pre-divisor constructions.
