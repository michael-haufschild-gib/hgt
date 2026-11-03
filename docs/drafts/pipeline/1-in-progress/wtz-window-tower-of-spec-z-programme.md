# The Window Tower of Spec ℤ (WTZ) — programme card

- **ID:** WTZ
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0211/obstacles-summary.md §2.7 (theory of the window tower)
- **Statement:** develop the tower `A ↦ W_A`: window algebra, transitions and control, Tate pieces
  vs Weil's form, lattice, growth, symmetries, selection.

## Goal
Answer the §2.7 questions by Lean theorems; build the tools. Folder
`formal/GaloisForLFunctions/WindowTowerOfSpecZ/`, umbrella `WindowTowerOfSpecZ.lean`, README there.
CWS (`CohomologyOfWindowsOfSpecZ`) is owned by another agent: import, never edit.

## Lean modules [L]
TheWindowDirichletAlgebra, TheTowerOfSmallExtensions, TheWindowFormIsTheDerivativeOfTheJordanCounts,
TheTateFlowOnTheWindowAlgebra, TheAtomicLatticeOfAWindow, TheExactPoleCapacityOfAWindow,
TheSymmetriesOfTheTower, TheTwistsOfTheTower, WeilsWindowFormIsASignedCount,
TheTransferAcrossAStage, TheExitChargePaysEveryNewFold, TheEulerFactorizationOfAWindow,
TheEndProfileOfAWindow, ShortWindowsArePaidByTheirExitCharge, TheArakelovBundleOfAWindow,
TheAtomicLatticeSeesTheMertensSum, TheValuationAndTheUnitsOfTheTower,
TheTangentPrincipleOfTheTateFamily, TheHilbertFunctionOfTheTower.

## Status
- Window algebra = Dirichlet ring truncated at `⌊e^A⌋` (`ker_windowRep`); nesting; `ZMZ⁻¹ = M − ρ(Λ)`;
  `Q = Ω‖H‖² + J − 2⟨ρ(Λ)H,H⟩ + pole`.
- Control: small extensions, socle law, sharp Loewy length, cotangent = primes, inverse limit.
- Tate: `J_0 = 1`, `∂J|₀ = Λ`, `J_{β+1} = φ#ℙ^β`, `Q = Ωτ(0) − 2τ′(0) + J + pole`; first prime coefficient
  `#ℙ^{k−1}(𝔽₂)`; cocycle, commutator form, Hensel tower; flips fail and `ζ(s)ζ(s−ε)` passes Tate positivity.
- Atomic lattice = regular representation; arithmetic = multiplication by `Λ`; pole = values at `s=0,1`.
- Exact pole capacity `2sinh(A/2) − A`; sharp floor `≤ −Ω(0) + (4A+1)e^{A/2}`.
- Adams lifts = dilations up to Tate twist `(e−1)/2`; Serre duality = Rosati involution.
- Character twists carry Tate families: `L(s,χ)` has Tate pieces `χφ#ℙ^β`, non-Tate piece `χΛ`; near
  dimension zero Tate positivity at primes ⇔ weight sign (Markov, soft).
- Signed count: `Λ(n) = Σ p_j J_j(n)` for `P` interpolating `log` on `1..N`; `Q = Ω‖H‖² + J + pole − 2Σ p_jτ(j)`.
- Stage transfer: `Q = Q_N + w(fold − end mass)`; composite stages free; collar exit charge
  `Ω(ε)∫_{collars}H² ≤ J_∞` with `Ω(ε) ≥ log 3 > 2/e ≥ w_n` on every stage: every new fold is paid.
- Euler factorization of the window zeta operator (factored indicators, `e_p(1−δ_p) = 1`).
- End profile: `∫(Ω(−u)+Ω(A+u))H² ≤ J_∞`; `Q ≥ ∫V_A H² + pole`, `V_A = Ω_Γ + φ(d₋) + φ(d₊)`;
  windows of length `≤ 1/7` positive by the exit charge alone.
- Arakelov bundle `⊕_{m≤e^A}𝒪(½log m)`: RR `Nd + ½log N!`, slope `≤ A/2`.
- Algebra: stage valuation, Wiener's lemma, Hilbert function = almost-prime counts, socle `(N/2,N]`,
  Gorenstein iff `N ≤ 2`. Tangent principle `J_k ≥ [n=1] + kΛ`. Atomic arithmetic ≤ Mertens sum.

## Open (README §7)
Positivity surviving the derivative at dimension zero; positivity across a small extension;
stage-resolved analytic control (AOT aperture transport); window capacity; exponent vs zero width.

## Log
- 2026-11-02 — created; fifteen modules formalized; README written.

## Conjecture loop (ledger)
| # | Conjecture | Test | Status |
|---|---|---|---|
| C1 | On the atomic lattice `|⟨ρ(Λ)ιg,ιg⟩| ≤ ½(Σ_{d≤N}Λ(d)/d + log N)‖ιg‖²` (Mertens size, not `ψ_{1/2}`) | numerics: λ_max ≈ ½ Mertens (N ≤ 3000) | **[L]** `TheAtomicLatticeSeesTheMertensSum` |
| C1' | sharper: λ_max ≤ ½ log N | numerics N ≤ 3000 (ratio → ½ from above vs Mertens; `≤ ½ log N` holds) | open (needs Mertens `Σ Λ/d ≤ log N`) |
| C2 | stage multiplicativity: `v(f*g) = v(f)v(g)`, leading coeff multiplies; exact nilpotency order | paper | **[L]** `TheValuationAndTheUnitsOfTheTower` |
| C3 | Wiener's lemma: `ρ_A(f)` unit ⇔ `f(1) ≠ 0`; spectrum `{f(1)}` | paper | **[L]** same module |
| C4 | tangent principle `J_k(n) ≥ [n=1] + kΛ(n)` (k ≥ 0) ⇒ nonneg tests: `⟨ρΛH,H⟩ ≤ (τ(k) − ‖H‖²)/k` | paper | **[L]** `TheTangentPrincipleOfTheTateFamily` |
| N0 | numeric window model (sine basis, Lévy symbol from ω): μ(0.3)=0.225, μ(0.6)=0.0086, μ(0.8)=2e−4, ≈0 beyond 1 | harness `weilwin.py` | tool; precision ~1e−3 |
| C5 | archimedean index `ι_Γ(A)` = #neg squares of `Ω_Γ + J_∞` on the window: `0` below `A₁ ≈ 0.215`, `1` on `(A₁, A₂ ≈ 0.762)`, then `≈ 2A` (Weyl, symbol zero `ξ₀ ≈ 2π`) | numerics `archindex.py` | observed; second (odd) direction appears after `log 2` |
| C5' | pointwise-in-`J` mechanisms cannot pass `A₁ ≈ 0.215` (true ground energy of `Ω_Γ + J_∞` crosses 0); Picone parabola weight reaches ≈ 0.20, exit potential 0.18 | numerics `picone.py` | learned: beyond `A₁` the pole is indispensable |
| C6 | `m^k + I_N = {f : f(n)=0 for n ≤ N, Ω(n) < k}`; `gr_k` has basis the `k`-almost primes ≤ N (Hilbert function = Landau `π_k(N)`) | paper | **[L]** `TheHilbertFunctionOfTheTower` |
| C7 | socle of `D_N` = span `δ_n`, `N/2 < n ≤ N` (type `⌈N/2⌉`); Gorenstein ⇔ `N ≤ 2` (window `< log 3`) | paper | **[L]** same module |
| C8 | parity at the first prime: on `[log 2, log 3)` the fold `T₂` raises the σ-odd sector and lowers the σ-even sector; pole does the opposite | numerics `parity.py` (odd min −0.013→+0.030 at A=0.76) | observed |
| C9 | every test (not only `H ≥ 0`) is dominated by the Tate counts of its modulus: `Q ≥ Ω‖H‖² + J + pole − (2/k)(τ^{|H|}(k) − ‖H‖²)` | paper | **[L]** `weilQuad_ge_absTateCount` |
| C10 | `ζ ≡ exp ℓ`, `ℓ = Λ/log`, on every window; `ρ(Λ) = [M, log Z]`; `J_k ≡ exp g_k`, `g_k(p^a) = #(𝔸^k∖0)(𝔽_{p^a})/a` (Hasse–Weil of punctured affine space); `J_k ≥ [n=1] + g_k ≥ [n=1] + kΛ` | paper (log-derivation ODE uniqueness on `D_N`) | **[L]** `TheTateFamilyIsAnExponentialOfPointCounts` |
| C11 | Tate positivity horizon: `ρ_A(J_k)` PSD only for `k < k*(A)`, `k*(0.8) ∈ (1,2)`, `k*(2) ∈ (½,1)`, `k*(3) ∈ (¼,½)` → 0 | numerics `tatepsd.py` | observed; only the tangent at 0 is uniform |
| C12 | pole-free form: Perron ground state ≈ −canonical degree, rest of spectrum ≈ 0⁺ (RH ⇒ index ≤ 1) | numerics `polefree.py` | observed (precision-limited for A > 2) |
| C13 | Weyl law for the archimedean index: the Gamma symbol `Re ψ(¼+iξ/2) − log π` vanishes at `ξ₀ = 6.2898 ≈ 2π`; critical lengths `A_k` = 0.218, 0.7635, 1.2506, 1.7619, 2.2574, 2.7617, 3.2600, gaps → `π/ξ₀ ≈ ½`, `A_k ≈ k/2 − 0.24`; `ι_Γ(A) ≈ 2A` | numerics `weyl.py` | observed (the `2π` of Riemann–von Mangoldt) |
| C14 | jets of the Tate family at dimension 0 are Bombieri's `Λ_j = log^j * μ`; EGF `J_k = Σ k^jΛ_j/j!`; `Λ_{j+1} = Λ_j log + Λ*Λ_j`; `Λ_j ≥ 0`, `Λ_j(n) = 0` for `ω(n) > j`; Selberg `Λ₂` = second jet | paper | **[L]** `TheJetsOfTheTateFamily` |
| C15 | a datum with logarithm `g ≥ 0` (`DF = Dg·F`) is Tate positive in every real `k ≥ 0` at every `n`: `J^F_k ≥ [n=1] + g(n^k−1)`; shifted datum has `g = ℓ(1+n^ε) ≥ 0`; flips (`ℓ_F(p) = −1`) and quadratic `L(s,χ)` fail ⇒ the sign of the logarithm does not select | paper | **[L]** `TheLogarithmOfAnEulerDatum` |
| C16 | critical Perron state: `pole(h_A)/|λ₀(A)| → 1⁺` (1.068, 1.053, 1.016, 1.009, 1.008, 1.004, 1.003, 1.002, 1.001 at A = .5 … 4); RH ⇒ ratio ≥ 1 | numerics `perron.py` (error ~1e-3 at A ≥ 2) | observed: the pole lifts the Perron state to an asymptotic null vector |
| C17 | Tate positivity horizon law `k*(A)·e^{A/2} → ≈ 1.66` (k* = 1.94, 1.20, 1.05, .735, .516, .384, .291, .224, .175 at A = .8 … 4.5); provable lower bound `kN^kψ_{1/2}(N) ≤ log 2 ⇒ ρ_A(J_k) ≥ 0` via `J_k = exp g_k` and submultiplicativity of `Σ f(n)/√n` | numerics `horizonk.py`; paper | **[L]** lower bound `TheTatePositivityHorizon`; exact constant open |
| C18 | Tate function log-convex at 0 for nonneg tests (`T₁² ≤ T₀T₂`, Weil term bounded by Selberg jet) | wide tests: `T₁ ≈ 2√N`, `T₂ ≈ 4√N log N` ⇒ `T₁² ≫ T₀T₂` | **refuted**; learned: Cauchy–Schwarz between jets loses `√N` |
| C19 | prime-free Weil min eigenvalue at `A = log 2` | numerics `conv.py`: 0.001511 → 0.001466 → 0.001428 → 0.001407 (K = 16 … 48) | ≈ 0.0014 > 0 (CC positivity margin at the first prime) |
| C20 | λ-ring form: `ℓ ≡ Σ_a ψ^a(P)/a`, `ζ ≡ PE[P]`; `Λ ≡ Σ_a ψ^a(P_log)`; tower recursion `ρ_A(Λ) = Σ_a D_aρ_{A/a}(P_log n^{−(a−1)/2})D_a^{−1}` | paper | **[L]** `TheWindowZetaIsAPlethysticExponential` |
| C21 | prime-only Weil form (drop all prime powers) negative from `log 4` on: −0.096 at A = 1.5, index 4/9/14/21 at A = 2/2.5/3/4 | numerics `primeonly.py` | observed: prime powers are indispensable at their entrance |
| C22 | fold rigidity: dropping (`Λ(n) → 0`) or doubling (`→ 2Λ(n)`) any single fold `n ≤ 16` makes Weil's form negative within `0.2` of `log n` (drop: −0.18 … −0.57; double: −0.14 … −0.67) | numerics `dropfold.py`, `rigidity.py` | observed: admissible `λ` for `Λ(2) → λΛ(2)`: [0, 2.24] (+0.06), [.61, 1.62] (+0.10), [.86, 1.30] (+0.15), [.964, 1.092] (+0.25), [.980, 1.012] (+0.40), [.991, 1.008] (+0.60, tolerance floor); same for `n = 3`. Explanation: Weil's spectral measure vanishes on the zero-free band `|ξ| < γ₁ = 14.13`; a single-fold change adds `±2c n^{−1/2}cos(ξ log n)`, negative inside the band, seen once the window resolves the band. Unconditional in principle (no zeros below height 14) |
| C23 | spectral fingerprint of the tower recursion: removing the Adams component `ψ^a(P_log)` (the `a`-th powers of primes) creates negative directions at frequencies `γ/a` (`ζ'/ζ(as)` has singularities at `ρ/a`, real part `1/(2a)`) | numerics `pofreq.py`, `dropcubes.py`: drop squares → modes at 7.07 (= γ₁/2), 10.68 (≈ γ₂/2 = 10.51); drop cubes → 4.71 (= γ₁/3 exactly), 10.5 | observed; explains C21 and C22 |
| C24 | isolation of `Λ`: for every nonzero finitely supported `δ` on `n ≥ 2`, `Λ` and `Λ + δ` are not both Weil-positive on all windows | paper sketch: the perturbation adds `−2Σδ_n n^{−1/2}cos(ξ log n)`, an almost-periodic function of mean zero, negative on an interval `I`; if `Λ` is positive (RH) its spectral side is `Σ_γ`-point masses, so wave packets of frequency in `I∖{γ}` on long windows make `Q_{Λ+δ} < 0` | paper sketch; Lean needs the explicit formula with zeros (not in WTZ) |
| C25 | frozen datum `Q_N` minus collar charge stays ≥ 0 | C22 numerics at every stage n ≤ 16; first stage proved by the other WTZ agent (`exists_first_stage_positive_exit_loan_failure`) | **refuted**; the new fold's energy is indispensable |
| C26 | exact first-stage Tate horizon: on `log 2 < A < log 3`, `ρ_A(J_k) ≥ 0` iff `2^k ≤ 1 + 2√2` (`k* = log₂(1+2√2) = 1.93675`); extremal test = two opposite collar atoms | numerics: window 1.9369, atomic 1.9368; paper: `|c₂| ≤ ‖H‖²/2` by collar disjointness, equality for bump minus translate | **[L]** `tateFunction_nonneg_iff_firstStage` |
| C27 | atomic Tate horizon `≈ 1.56/log N` (N = 20 … 1000), strictly above the window horizon for `N ≥ 3` | numerics `atomhorizon.py` | observed; atoms are extremal only at the first stage (cf. C1) |
| C28 | exact second-stage horizon (`log 3 < A < log 4`): threshold of the weighted path `P₄`: `x+log(3/2) —2— x+log 3 —3— x —2— x+log 2`, `λ_max(P₄(a₂,a₃,a₂)) = 1`, `a_n = (n^k−1)/(2√n)`: `k* = 1.199668` | numerics `stage2.py`: 1.1997 for A ∈ [1.2, 1.38]; the atomic value 1.2639 is the star graph `{1;2,3}` | **[L]** lower bound (`two_mul_abs_autocorr_add_le`, `tateFunction_nonneg_secondStage`: positive iff `α² + β ≤ 1`, path Picone with Perron weights; sharp by C32) |
| C29 | orbit-graph principle: an arithmetic window form `Σ w_n T_{log n}` is a direct integral over finite orbit graphs of the fold groupoid (vertices `x + Σ a_p log p` in the window, edges = folds); positivity/horizon = min over the graphs fitting in the window | C26 (P₂), C28 (P₄), C27 (atoms = stars) | conjecture; this is the graph Schur-complement structure of obstacles §2.7 |
| C30 | sharp arithmetic bound at the second stage: `|w₂c₂ + w₃c₃| ≤ r‖H‖²`, `r = (w₃ + √(w₃² + 4w₂²))/4 ≈ 0.4505` (pointwise canonical density gives `w₂ + w₃ ≈ 1.124`) | path Picone | **[L]** `abs_arith_secondStage_le` |
| C31 | Tate horizon staircase: `k*(A)` is non-increasing and drops inside stages as new orbit graphs fit (stage 3: 1.0504 (1.45), 1.0458, 1.0263, 1.0162 (1.60); stage 4: .9151, .8284, .8208; stage 7: .7703, .7109, .6720) | numerics `staircase.py` | observed: critical lengths are combinations of logs, not only `log n` |
| C32 | sharpness of the second-stage path: bumps `(α, −1, 1, −α)` on the path vertices give `2(1 − α² − β)‖φ‖²` | paper | **[L]** `exists_neg_secondStage`, `secondStage_nonneg_iff`, `tateFunction_nonneg_iff_secondStage` |
| C33 | rational-configuration principle: the Tate horizon `k*(A)` = PSD threshold of the weighted Hecke graph on the rationals of `[1, e^A)` reachable from `1` by `×n, ÷n` (`n ≤ e^A`), weights `J_k(n)/(2√n)` | numerics `ratgraph.py`: A = 1.50: graph 1.0457 / window 1.0458; 1.60: 1.0157 / 1.0162; 2.30: 0.5829 / 0.5819 (graph capped at 2000 vertices); window numerics are upper bounds, under-resolved where configurations need narrow bumps | confirmed to 3–5 digits; the orbit graphs of C29 are the finite configurations of `ℚ_{>0}^×` in the window, i.e. the Hecke operator of `ℤ[ℚ_{>0}^×]` truncated to the window (obstacles §2.7 tool) |
| C34 | rational lattice: every finite `S ⊂ ℚ_{>0}` of spread `< A` is realized by disjoint bumps with `∫ι(u)ι(u + log n) = ‖φ‖²Σ_{s = nr} y_r y_s`; every arithmetic window form equals the Hecke graph form on `S` | paper | **[L]** `exists_rationalLattice`, `exists_windowTest_eq_heckeForm` (upper-bound half of C33) |
| C35 | no uniform Tate positivity: for every `k > 0` some window has `τ_H(k) < 0`; witness = star `{1} ∪ {p ≤ M}` of the rational lattice with `y₁ = 1`, `y_p = −J_k(p)/(2√p)`, value `1 − Σ_p J_k(p)²/(4p)`; `Σ 1/p` diverges | paper | **[L]** `exists_tateFunction_neg_of_primeSum`, `exists_tateFunction_neg` |
| C36 | graph canonical degree: the sharp bound `|⟨ρ_A(Λ)H,H⟩| ≤ g(A)‖H‖²` is the spectral radius of the `Λ`-Hecke graph of the rational lattice; `g` = 0.2451 (stage 1, exact), 0.4505 (stage 2, exact), 0.586, 0.829, 0.970, 1.231, 1.488 at A = 1.5 … 2.6 (vertex-capped), i.e. `≈ 0.3–0.4 ψ_{1/2}(e^A)`, `g e^{−A/2}` rising 0.16 → 0.41 | numerics `lamgraph.py` | observed; improves the constant of the floor (pointwise `ψ_{1/2}`-scale), not its exponent |
| C37 | window Barta criterion: a measurable weight `1 ≤ h ≤ C` balancing the folds (`Σ a_n(G(u+ℓ_n)+G(u−ℓ_n)) ≤ h(u)`) gives `Σ 2a_n|c_n(H)| ≤ ‖H‖²`; conjecture: a balanced weight exists iff every rational Hecke graph of the window has spectral radius ≤ 1 (Allegretto–Piepenbrink for the window) | paper | **[L]** criterion (`sum_two_mul_abs_autocorr_le`, `arith_form_nonneg_of_balanced`); converse open |
| C38 | ground-state transform of a window: Picone jump weight `a_h(y,u) = 2 − (G(u+y)+G(u−y))/h(u)` satisfies `∫a_hH² ≤ ∫(H−H(·+y))²`; for balanced `h` (`a_h ≥ 0`) and `V ≤ ∫ω a_h`, `∫VH² ≤ J_∞(H)`; with the fold Barta bound `Q ≥ (Ω_Γ − κ)‖H‖² + ∫VH² + pole` | paper | **[L]** `integral_piconeWeight_mul_le`, `integral_mul_le_levyJump_of_picone`, `weilQuad_ge_groundState` |
| C39 | rigidity scale: the admissible interval of a single fold weight tightens between `A − log n = 0.15` and `0.25` for both `n = 2, 3` (widths 0.44/0.18 → 0.13/0.04), i.e. at `A − log n ≈ π/γ₁ = 0.222`, the length at which a window resolves the zero-free band | numerics C22 | observed; the rigidity scale is set by the first zero, uniformly in `n` |
| C40 | what `sym_n` counts: on the indicator of a rational configuration `S`, `∫ι(u)ι(u+log n) = ‖φ‖²#{r ∈ S : nr ∈ S}` (multiplicative `n`-pairs inside `S`) and the fold energy is `‖φ‖²` times the number of `n`-edges cut by `S` | paper | **[L]** `integral_ratLattice_one_eq_card`, `foldEnergy_ratLattice_eq_card` |
| C41 | reflection positivity of Weil's window form along `σ_A` (Mechanism D): `B(f, σ_Af) ≥ 0` for `f` on the left half | numerics `reflpos.py`: min eig −0.548 (A = 0.5, Gamma + pole only), −0.94/+0.94 at A = 1.5 with primes | **refuted** in both signs: the Lévy cross kernel `ω(x + y)` is completely monotone, so the archimedean part is reflection *negative*, and the folds make the cross form indefinite; a placement positivity needs a different reflection |

