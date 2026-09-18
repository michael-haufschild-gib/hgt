# `(L)` at the microscopic scale: conjecture loop against the bandwidth / mollifier-length wall

- **ID:** L-MICRO-LOOP-001
- **Stage:** 1-in-progress (loop record; no producer found in cycle 1)
- **Type:** CONJECTURE LOOP (verdicts), no Lean target selected
- **Source:** frontier map (all 25 active routes end in "source production"); memory notes
  `offline-first-moment-mollified-ceiling`, `steinhaus-jensen-floor`, `offline-isolation-dichotomy`,
  `critical-proportion-external-sota-2026`; cards `offline-density-zero-detector-barrier.md`,
  `zeta23-beyond-bandwidth-one-proportion.md`, `claude-zeta23-rank-trace-audit.md`.
- **Target:** `(L)`: `Σ_{0<γ≤T} m_ρ (β−½)⁺ = o(T)`, equivalently `(1/T)∫_0^T log|ζ(½+it)| dt → 0`
  (Littlewood + the corpus floor). Strictly weaker than RH, strictly weaker than "almost all zeros
  on the line" (AAL), open (Najnudel–Nikeghbali 2609.15862 Thm 8.7 treats it as a hypothesis).

## The wall, stated exactly (cycle 1, 2026-09-18)

Write `a_ρ = (β−½)·log T` for the displacement in mean-spacing units and
`p_T(a)` for the proportion of zeros with `a_ρ > a`.

1. `(L) ⟺ ∀ε>0: N(½+ε/log T, T) = o(N(T))` (microscopic horizontal collapse; NN Prop 8.5).
   Proof sketch both ways: `Σ(β−½)⁺ ≥ (ε/L)·#{a_ρ>ε}`; conversely split at `a = ε` and `a = A`,
   the far part `Σ_{a>A}(β−½)` is `O(T e^{−A/4})` by Selberg's density. Also
   `(L) ⟺ Σ_ρ a_ρ² = o(N(T))` (Cauchy–Schwarz one way, Selberg's tail the other way).
2. What the corpus certifies about the profile: `p_T(0⁺) ≤ 1/3` (Zeta23 two-thirds, Lean);
   `p_T(a) ≤ 2.4 e^{−8a/7}` (paper, Conrey `θ = 4/7`; trivial for `a < 0.77`);
   `∫ p_T(a) da = Σ a_ρ / N ≤ 0.336` (MUST-349 ceiling `0.0535T`). `(L)` is `p_T(a) = 0` for every
   fixed `a > 0`; nothing certified says anything for `0 < a < 0.77` beyond the count `1/3`.
3. Every certified detector is one of: mollified Littlewood on a shifted line (mean-square gate at
   mollifier length `θ < 4/7`; Jensen floor `log c(R,θ) > 0`; CANNOT-300…305), pair correlation
   at bandwidth `α ≤ 1` (BGSTB analytic `F`, Montgomery–Taylor / rank–trace; support-1 ceiling
   `0.6725`), or zero-density at fixed `σ > ½` (Guth–Maynard exponent; blind below `1/log T`).
   The barrier card proves the resolution of all smooth polynomial-scale detectors is `Θ(1/log T)`.
   Consequently `(L)`, AAL, `κ → 1`, `p_T(a) → 0` at fixed `a`, and the 75% programme's source
   estimate `(HC75)` are all the SAME open problem: information at mollifier length `θ → ∞` or
   pair-correlation bandwidth `α > 1`, which by Goldston–Montgomery is prime-pair-correlation
   (variance of `ψ` in intervals of length `x^{1−1/α}` with the sharp constant).

## Conjectures tried this cycle and verdicts

- **C1 (cosh-excess in the analytic pair sum).** For `η ≥ 0` even and `F = η̂²`, the orbit block of a
  reflected pair `{ρ, 1−ρ̄}` in `A(η) = Σ_{ρ,ρ'} η̂((ρ−ρ')/i)²` equals `2g(0)² + 2g(2δ)²` with
  `g(v) = ∫η e^{vx}`, exceeding the projected block `4g(0)²` by `≥ 8δ²(∫η)(∫ηx²)`; in the Hilbert-space
  picture (`e_z = √η e^{izx}`, PSD Gram) the pair is two vectors at angle `≍ δ·std_η(x)`, the
  `2×2` Gram minor is `g(2δ)g(−2δ) − g(0)² = 4δ²(∫η)²Var_η(x) + O(δ⁴) > 0`. Conjectured use:
  `A − B = excess + cross` with `B` the projected (MT) pair sum, `A` known unconditionally (BGSTB,
  `0 ≤ α ≤ 1`), hence a second-moment bound `Σ a_ρ² ≪ N` at bandwidth 1 and, if sharp, `(L)`.
  **Verdict: FALSE as a producer (cross blocks unsigned).** The distinct-ordinate orbit blocks are
  `2Re φ_{δ−δ'}(u)² + 2Re φ_{δ+δ'}(u)²`, `φ_v(u) = C_v(u) + iS_v(u)`, `C_v = ∫η cosh(vx)cos(ux)`,
  `S_v = ∫η sinh(vx)sin(ux)`; `Re φ_v² − C_0² = (C_v² − C_0²) − S_v²` has no sign. Even the
  favourable bound `Σ_{a≤1} a² ≤ 0.33N/(4m₂)` would only match the first-moment consequence
  `Σ_{a≤1} a² ≤ 0.336N`. In the rank–trace machine the trace of a pair block is `δ`-independent for a
  tight frame; displacement enters only the Frobenius norm and the indefiniteness. Same as the
  corpus note "unconditional Montgomery cannot bound the off-line diagonal".
- **C2 (one-sided pair correlation beyond bandwidth 1 from sieve bounds).** MT needs only an upper
  bound `∫_1^A F(α) r̂(α) dα`; `F ≥ 0`; sieve upper bounds for `Σ_n Λ(n)Λ(n+k)` are unconditional.
  **Verdict: FALSE.** The variance `V(h,X)` must be known to precision `hX log(X/h)`; the sieve bound
  leaves an error `≍ 3h²X ≫ hX log X` (the off-diagonal main term must cancel exactly). Density
  theorems (Huxley, Guth–Maynard) give `V = o(h²X)`, also useless at the sharp scale.
- **C3 (small-`k` moment characterisation).** `(1/T)∫|ζ|^{2k} = 1 + 2k·m_T + O(k² log log T)` with
  `m_T = E log|ζ(½+it)|`, so `(L) ⟺` the sharp constants `C_k` in `∫|ζ|^{2k} ≤ C_k T(log T)^{k²}`
  satisfy `C_k = 1 + o(k)` uniformly down to `k ≍ 1/log log T`. Harper/HRS methods give `C_k = e^{O(k)}`
  from the Euler-product truncation error. **Verdict: BRIDGE** (a restatement; the linear term in `k`
  IS the log-mean; no independent handle).
- Also checked and rediscovered: sign changes of Hardy's `Z` (`N₀ˢ ≤ S₀ ≤ N₀`, Selberg lower bound),
  microscopic count variance `E|S(t+h)−S(t)|²` at `h ≍ 1/L` (its diagonal is `Σ_γ H_γ²`, needs primes
  to `T^{1/λ}`), Speiser/Levinson–Montgomery for `ζ'`, Jensen on discs (second order in displacement
  divided by `γ²`: blind), fractional/negative moments (corpus MUST-214: needs Gonek input + spacing).

## Loop verdict (cycle 1)

NO PRODUCER FOUND. Positive survivors (paper, exact): the microscopic second-moment equivalence
`(L) ⟺ Σ_ρ a_ρ² = o(N)`, and the Gram-angle law of C1 (displacement = angle between the pair's
two vectors, minor `4δ²(∫η)²Var_η(x)`). Neither is a Lean target: the first needs Selberg's density
with an exponential profile (the corpus's crude gate has no decay in `a`), the second has no consumer.
Next cycle must change class: a statement whose sensitivity does not degrade as `a → 0` and is not a
smooth functional of the zeros (the 75% card's `(HC75)` is the corpus's only such candidate, and its
source estimate is again bandwidth `> 1`).

## Log
- 2026-09-18 — cycle 1 run after the HB sign law closed; three conjectures, verdicts above; card created.

## Cycle 2 (2026-09-18): the "not a smooth functional" class

Candidates whose sensitivity does not degrade as `a → 0`, and why each returns to the wall:
- **Sign changes of Hardy's `Z`.** `S₀(T)` counts odd on-line zeros; off-line pairs never flip the
  sign. Counting sign changes needs, on almost every mean-spacing window, `∫|Zq| > |∫Zq|` for all
  polynomials `q` of the local degree: a local `L¹` floor for `Z` at scale `1/L`, which is Selberg's
  mollified argument with `κ → 1` (mollifier length `θ → ∞`). REDISCOVERED / same wall.
- **Negative-squares index of the Weil form.** In a Gabor compression a microscopic pair gives a
  `(1,1)` block with eigenvalues `2‖u‖² + O(δ)` and `−c δ²`: the index is discontinuous in `δ`, every
  polynomial spectral functional (`tr G^k`, so also the cubic trace) is continuous, and detecting
  the index needs a floor for `|λ₋| ≍ δ²`, i.e. displacement resolution. The AF/Zeta23 machine
  (trace + Frobenius + rank–trace) is therefore optimal in its class at `0.6725`; a third moment
  `tr G³` adds nothing at leading order. INSIGNIFICANT.
- **Sign-tracking by an AFE approximant.** Requires `|Z − Z̃| ≲ δ²|G|` in the window of a pair
  (else the approximant crosses zero): precision degrades with `δ`. Same wall.
- **HCF 75% receiver** (`three_quarters_line_of_boundaryVarianceTranslatedBudget`): the premise is
  a lattice sum of `criticalFeaturePrimeGammaOffLineExcess`, a zero-side observable; the card's own
  audit lists the closed classes ("fixed finite shifts lose arbitrarily shallow charge") — the
  shallow copies are the microscopic displacements. Not attempted.
- Corpus campaign logs already dedicated to the arithmetic wall: `lindelof-hypothesis-campaign`,
  `density-hypothesis-large-values-frontier`, `selberg-quarter-conjecture-corpus-audit`,
  `critical-multiplicative-compensated-cancellation-rh` (spectral/Kloosterman dispersion provider
  refuted). The corpus marks the Kuznetsov spectral average as missing
  (`Sieve/KloostermanSharedHybridCollapse`).

Verdict cycle 2: NO PRODUCER FOUND. The only escape from the wall is arithmetic input beyond
bandwidth one (prime pair correlation with the sharp constant, or twisted moments with
`θ > 4/7`); no non-arithmetic reformulation changes the required resolution.

## Cycle 3 (2026-09-18): the negative-squares index lane

- Apex card `0-backlog/carrier-herglotz-rh.md`: RH ⟺ `m_ξ = −Ξ′/Ξ` Herglotz (`κ₋ = 0`); the
  finite anchor `κ₋ = #off-line pairs` is Lean (`multiPair_carrier_exact_neg_inertia`); the
  "infinite passage" needs one archimedean rigidity bound forcing `κ₋ = 0`, i.e. RH itself.
- Corpus index laws (`carrierPickMatrix`, `…_exact_negativeSquares`, index inflation/fracture): finite
  prime-side apertures have cofinally unbounded negative index; the Herglotz property of the full
  carrier is a cancellation between prime atoms and the archimedean part, not a property of any
  finite prime truncation. So the index is exactly the discontinuous invariant of cycle 2, and a
  Pick matrix sees a microscopic pair only at nodes within distance `≍ δ` of its pole. Same wall.
- Mesoscopic cousin: `density-hypothesis-large-values-frontier.md` (545 theorems; open core 388:
  square-root cancellation of `∫_E x^{it}dt` over the large-value set `E` of a length-`N` Dirichlet
  polynomial, `x = n/m`). Literally false for a two-term `D` (`E` is periodic with period
  `2π/log(n/m)`, fully resonant), so the true statement must use the length; it is the geometry of
  large-value sets, the live 2024–26 area (Guth–Maynard, Chen–Gupta–Li). Not microscopic; does not
  reach `(L)`.

Verdict cycle 3: NO PRODUCER FOUND. Three cycles, three classes (smooth detectors, discontinuous
invariants, index/Pick), one wall. Continuations that are not theatre: (i) sharp variance of primes
in short intervals at one scale (microscopic wall, arithmetic), (ii) large-value-set geometry for
long Dirichlet polynomials (mesoscopic, DH open core 388). Neither has a corpus lead beyond the
campaign logs.
