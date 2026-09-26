# PM route (FZZ-P / PW-B) — reduction to prime-clock receivers

- **ID:** pm-physical-model-clock-reduction
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) + conjecture loop
- **Source:** docs/reports/rh-current-frontier-map.md §PM; F0077; fzz-p-own-research-facts.md; fzz-p-rbh-pw-b-ptr-source-facts.md
- **Statement:** The FZZ-P physical premise (divisor-mode passivity of the linear replica-area response) is exactly boundedness of the dyadic prime-clock pencil of the zeros.

## PM-1 (proved, Lean)
`RHTower/FZZParityAreaResponseDyadicClockBridge.lean`:
- `fzzAreaResponse_mellinTwist_eq_dyadicClockOrbitAverage`: at the canonical parity-Mellin twist
  `R(ρ) = 3/4 + (‖2^{ρ−½}‖² + ‖2^{(1−ρ̄)−½}‖²)/8` — the reflection-orbit average of the squared dyadic clock.
- `fzzAreaResponse_mellinTwist_le_one_iff_dyadicClock_unimodular`: passivity ⟺ `‖2^{ρ−½}‖ = 1`.
- `fzzLinearReplicaAreaDivisorPassive_iff_forall_dyadicClockExcess_bounded`: FZZ-P premise ⟺ for every strip
  window the Cesàro energy of `Σ_ρ m_ρ 2^{n(ρ−½)}` minus local squares is eventually bounded.
Build green, axioms standard, umbrella-wired.

**Meaning for the route.** The physical layer (cigar, replica area, torus twist) contributes nothing beyond
the prime-2 clock. The FZZ-P producer must bound the dyadic clock pencil of the zeros; by
`XiLineUnimodularClockExcessCriterion` an off-line zero makes that energy grow exponentially (no sub-unit
passivity margin), and its explicit-formula form is the single-base lag `Φ(m log 2)` (CANNOT-458).

## Conjecture loop
- PM-2 (open, genuine): single-base dyadic lag `sup_m a_{2^m} < ∞ ⟹ RH`; open exactly in the non-attained
  regime (`WeilLagFunctionSingleBase:riemannHypothesis_or_not_attained_of_forall_le`). Pringsheim on
  `Σ_m (M − a_{2^m}) z^m` (nonneg coefficients, poles `2^{½−ρ}`) forces: non-attained top zeros with dyadic
  phases `γ log 2/2π → 0 mod 1`. [paper; not yet Lean]
- PM-3 (to test): PW-B CTP extinction `Re CΣ = 0` at divisor copies is the unimodular-set receiver of the
  clock `exp(CΣ)`.

## PM-5 (proved, Lean) — deformation audit of the FZZ-P source
`RHTower/FZZParityDyadicNonPassiveModes.lean`: the literal parity-delay Mellin transform
`Γ(s)(1−2^{1−s})ζ(s)` vanishes at `s_k = 1 + 2πik/log 2` (k≠0) where the area response is `17/16 > 1`
(`not_forall_fzzParityMode_areaPassive`). A passivity law uniform over the modes of the literal parity
source is false; the parity regularization B(t)−2B(2t) buys holomorphy at s=1 with spurious non-passive modes.

## PM-6 (paper) — every finite dilation regularization has spurious modes
Σ_j c_j B(λ_j t) regular at s=1 has Mellin Γζ·P, P(s)=Σ c_j λ_j^{−s}, P(1)=0. Two terms: zeros exactly
1+2πik/log(λ₂/λ₁) (Re=1). J terms: almost periodicity + Rouché give infinitely many zeros near Re s=1.
Positive survivor: the singular-part subtraction B(t)−1/t has Mellin exactly Γ(s)ζ(s) on 0<Re s<1 (no
spurious modes) — but that is the sawtooth/Nyman–Beurling form ζ(s)/s = −∫{x}x^{−s−1}dx (CANNOT-LIN1).

## PM verdict (so far)
FZZ-P premise = zero-indexed dyadic clock pencil bound (PM-1); its literal source has non-passive spurious
modes (PM-5); the spurious-mode-free subtraction is Nyman–Beurling (PM-6). PW-B extinction is evaluated
only on zero copies (CΣ defined on `XiZeroCopy`); its missing all-divisor extinction law is the same
divisor-selective statement. No physical identity ties modes to zeros beyond the Mellin definition.

## PM-2 analysis (paper; open core confirmed)
Generating series G(z)=Σ_m(M−a_{2^m})z^m (nonneg coefficients; Vivanti–Pringsheim is in the corpus,
`HTGeometry.VivantiPringsheim`). F(z)=Σ_ρ c_ρ/(1−z·2^{ρ−½}), Re c_ρ>0 always (Re ρ(1−ρ)=¼−δ²+γ²>0), so
aliased residues never cancel. Missing step in the non-attained regime: the growth lower bound
limsup|a_{2^m}|^{1/m} ≥ 2^Θ; F can have a natural boundary (aliased poles 2^{½−ρ} fill arcs of the
annulus near |z|=2^{−Θ}), so neither Pringsheim at R nor residue arguments reach a pole. PM-2 stays open.

## Final PM insight
The canonical twist τ(ρ) = −(log 2/2π)i(ρ−½) is real exactly on the critical line. Physical passivity
of the replica-area response is automatic at real (physical) twists and has no content at complex ones;
the PM premise therefore asks physics to certify that divisor modes are physical — the Hilbert–Pólya
requirement (arbitrary real spectra are realizable; the content is the identification, 8.24/CANNOT-08).

## Log
- 2026-09-26 — created; PM-1 proved.

## PM-7 (paper) — source completeness is an outer-function statement
On the critical line every Mellin transform of a source is a matrix element of the unitary dilation group,
so no Hermitian identity on the line constrains off-line zeros. The literal PM receiver is one-sided: the dilates
`{f(λt) : λ ≥ 1}` of the parity source `f = B(t) − 2B(2t)` are complete in the Hardy-space picture iff its Mellin
transform `Γ(s)(1 − 2^{1−s})ζ(s)` is outer on `Re s > ½` modulo the explicit inner factor of `1 − 2^{1−s}`.
That factor is the Blaschke product over `s_k = 1 + 2πik/log 2` (`Σ ½/(1+|s_k|²) < ∞`; mean type 0, so no singular
factor). Completeness modulo that factor ⟺ RH, i.e. Nyman–Beurling for the Fermi/Bose kernel. The physical inverse
problem is the inverse blackbody problem, solved by Möbius inversion ⇒ PM ≡ route MC at the source level.

## PM-8 (paper, no-go) — Putnam-type Euler input cannot close PM-2
PM-2's non-attained counterexample needs, above every off-line zero, a sparse approximate comb of zeros at ordinates
`≈ γ₀ + 2πk/log 2` with nearly equal real part (shadow law). Putnam/van Frankenhuijsen exclude exact consecutive
vertical progressions. Their mechanism does not extend: approximate sparse dyadic combs occur generically on the
critical line (`γ log 2/2π` is equidistributed mod 1), so no Euler-product mean along the progression can see a
density-zero comb. The Bohr mean `lim (1/K)Σ_{k<K} ζ(s₀ + 2πik/log 2) = (1 − 2^{−s₀})^{−1}` excludes only positive-density
exact combs off the line. Landau's `Σ_{γ≤T} 2^{kρ} = −(T/2π)Λ(2^k)+O(log T)` is dominated by on-line zeros
(off-line count `o(T)`), so it is blind to the comb as well. Survivor: `NO POSITIVE SALVAGE` beyond the positive-density exact-comb
exclusion, which does not constrain the non-attained regime.

## PM status (2026-09-26, after PM-7/PM-8)
All PM receivers now land in routes with named open cores: dyadic clock → WL (`√X` one-sided prime bound);
source completeness → MC/Nyman–Beurling; PW-B extinction → nodal set of one reflection-odd Schwarz function
(the source-forced balance of the PW-B lane). PM-2 is the only non-circular PM question; it needs arithmetic
information about sparse sets of off-line zeros, which no known Euler-product identity supplies (CANNOT-327, PM-8).

## PM-9 (proved, Lean) — the divisor-selective Hermitian identity, explicit
`RHTower/FermiNymanBeurlingDyadicWitness.lean` (build green, axioms standard, wired).
The FZZ parity source in Nyman–Beurling form: generators `φ_a(x) = {1/(ax)} − 2{1/(2ax)}` (support `(0,1/a]`),
`M[φ_a](s) = −a^{−s}(1−2^{1−s})ζ(s)/s` on the strip and, by analytic continuation, on the punctured right half-plane.
Witness = continuous `w ∈ L²(0,1]` orthogonal to every `φ_a`, `a ≥ 1`.
- Spurious witnesses `t^{−2πik/log 2}` (`k≠0`) exist unconditionally and are dyadically self-similar `w(t/2)=w(t)`
  (`isFermiNymanWitness_spurious`, `powerWitness_spurious_half`).
- Zero witnesses `t^{ρ̄−1}` for zeros with `½<Re ρ<1`; `w(t/2)=2^{1−ρ̄}w(t)`, never self-similar.
- The witness class is invariant under the dyadic dilation `w ↦ w(·/2)` (`IsFermiNymanWitness.halfDilate`).
- Mass fractions: zero witness `∫_0^{1/2}|w|² = 2^{1−2Re ρ}∫_0^1|w|²`; self-similar witnesses exactly `½`.
- **Identity ⟹ RH (both forms):** every witness self-similar ⟹ RH (`riemannHypothesis_of_fermiNymanWitness_selfSimilar`);
  the Hermitian form `q(w) = ∫_0^{1/2}|w|² − ½∫_0^1|w|²` vanishing on all witnesses ⟹ RH
  (`riemannHypothesis_of_fermiNymanWitness_halfMass`).
- **FZZ bridge:** the canonical-twist area response of the mode `ρ` equals `3/4 + (m + m⁻¹)/8`, `m` = dyadic mass fraction of
  its witness (`fzzAreaResponse_eq_witness_massFraction`). Spurious modes are `m = ½` (response 17/16); off-line zeros
  have `m ∈ (½,1)` (response in `(1,17/16)`); critical zeros have no normalizable witness.
Meaning: the FZZ-P premise is exactly the statement that every normalizable witness of the physical source is a
dyadic (prime-2 Euler factor) mode. Open converse: RH ⟹ witness class = closed span of spurious witnesses
(Beurling-type completeness modulo the explicit Blaschke factor; paper-level via Hardy-space factorization).
Literature: η-variants of Nyman–Beurling exist; the spurious dyadic witness family, the dyadic invariance, the
mass-fraction Hermitian identity and the FZZ bridge were not found.

## PM-11 (proved, Lean) — the physical target is the dyadic Haar function
`RHTower/FermiNymanBeurlingHaarTarget.lean` (build green, axioms standard, wired).
`h = −1` on `(0,½]`, `+1` on `(½,1]`; `∫_0^1 h(t) t^{s−1} dt = (1 − 2^{1−s})/s` (`integral_dyadicHaar_mul_cpow`).
- `h` annihilates every spurious witness (`integral_dyadicHaar_mul_conj_spurious`) and pairs nonzero with every
  zero witness in the strip (`integral_dyadicHaar_mul_conj_zeroWitness_ne_zero`).
- Finite combinations of generators are orthogonal to every witness; complex Cauchy–Schwarz gives the floor
  `∫_0^1 |h − Σ c_j φ_{a_j}|² ≥ (2Re ρ − 1)|1 − 2^{1−ρ}|²/|ρ|²` for every zero with `½<Re ρ<1`
  (`dyadicHaar_approximation_floor`).
- **Criterion:** `h` an `L²(0,1]`-limit of alternating generators ⟹ RH (`riemannHypothesis_of_dyadicHaar_approximable`).
Meaning: on `Re s = ½` the distance is `(1/2π)∫|1−2^{1−s}|²|1 + ζ(s)D(s)|²/|s|²`, `D = Σ c_k k^{−s}`; since
`|1 − 2^{1−s}| ∈ [√2−1, √2+1]` there, the physical problem is the Báez-Duarte problem with a bounded equivalent weight.
The spurious factor cancels exactly against the Haar target; the physical model contributes the weight and nothing else.
Open core (unchanged): exhibit `D_N` with `‖1 + ζ D_N‖ → 0` — Möbius cancellation at the half power (route MC).

## PM-12 (proved, Lean) — one-sided positivity suffices; the generators are odd-floor indicators
`RHTower/FermiNymanBeurlingWitnessSignature.lean` (build green, axioms standard, wired).
- The witness class is a complex vector space (`IsFermiNymanWitness.add_smul`).
- Cross term of a spurious and a zero witness: `B(g_k, w_ρ) = (2^{−ρ} − ½)/(conj s_k + ρ − 1) ≠ 0`
  (`crossTerm_spurious_zeroWitness`); `q(g_k) = 0`, `q(w_ρ) > 0`, so `g_1 + ε w_ρ`, `ε = −B/q(w_ρ)`, has `q < 0`:
  an off-line zero makes the form indefinite by interference with the prime-2 modes.
- **Positivity criterion:** every witness has at least half its `L²` mass on `(0,½]` ⟹ RH
  (`riemannHypothesis_of_fermiNymanWitness_halfMass_le`). Equivalently (`q = ½(‖Tw‖² − ‖w‖²)`, `Tw = w(·/2)`):
  the dyadic dilation is non-contracting on witnesses ⟹ RH; zero witnesses are expanded (`2^{1−β}`), spurious ones fixed.
- `φ_a(t) = −1_{⌊1/(at)⌋ odd}` (`fermiNymanGen_eq_oddFloor`): witnesses are exactly the square-integrable functions with
  zero integral over every dilate `λE₁`, `0<λ≤1`, of the odd-floor set `E₁ = {t ∈ (0,1] : ⌊1/t⌋ odd}`
  `= (½,1] ∪ (¼,⅓] ∪ (⅙,⅕] ∪ …`. Differentiating in `λ`: `Σ_{m≥1} (−1)^{m+1} w(λ/m)/m = 0` — the kernel of the
  dilation operator `η(S)`.
Meaning: the physical identity is a statement about one explicit set `E₁` and its dilates. RH ⟸ the indicator
functions `1_{λE₁}` (`λ ≤ 1`) approximate the dyadic Haar function in `L²(0,1]` ⟸ no square-integrable function with
zero integral on all `λE₁` puts more than half its mass on `(½,1]`.

## PM-13 — the `L^p` ladder (Lean easy direction; paper endpoint)
[L] `no_zeta_zero_of_fermiNymanWitnessLp_selfSimilar`: if every `L^p(0,1]` witness of the alternating system is
dyadically self-similar, `ζ` has no zero with `1 − 1/p < Re ρ < 1` (zero witness `t^{ρ̄−1} ∈ L^p` iff `Re ρ > 1 − 1/p`).
`p = 2`: RH. `p = ∞`: obstructions only from zeros on `Re s = 1`, i.e. the PNT input `ζ(1+it) ≠ 0`.
[P] `p = ∞` endpoint holds unconditionally: a bounded witness `w` has Mellin transform `W` with
`(1 − 2^{−z})W(z) = −2^{−z}Φ(1−z)/ζ(1−z)` (`Φ(s) = s∫_1^∞ λ^{−s−1}F(λ)dλ`, `F(λ) = ∫ 1_{λE₁} w`), entire; with
`1/ζ(1+it) = O(log t)`, the horizontal-line bound for `1/ζ` and Phragmén–Lindelöf, `U(z) = 2^z ∫_0^{1/2}(w(t)−w(2t))t^{z−1}dt`
is an entire function of polynomial growth tending to 0 on the real axis, so `U ≡ 0`: bounded witnesses are
self-similar. So the physical identity is the PNT on `L^∞` and RH on `L²`; this is Beurling's `L^p` criterion
transported to the Fermi source. Consequence: RH ⟺ bounded witnesses are dense in the `L²` witness class.
Barrier (matches STATUS "exponent, not constant"): no method gives self-similarity of `L^p` witnesses for any
`p < ∞`, which would be a zero-free half-plane `Re s > 1 − 1/p`.

## PM-14 (paper → Lean in progress) — bounded witnesses are self-similar (the PNT end of the ladder)
Statement: `w` continuous on `(0,1]`, `|w| ≤ M`, `∫_0^1 φ_a w = 0` for all `a ≥ 1` ⟹ `w(t/2) = w(t)` on `(0,1]`.
Proof.
1. `F(a) = ∫_0^1 φ_a(t) w(t) dt` (`φ_a(t) = φ_1(at)`), `|F| ≤ 3M`, `F = 0` on `[1,∞)`.
   `Φ₀(s) = ∫_0^1 a^{s−1}F(a) da` analytic on `Re s > 0`, `|Φ₀(s)| ≤ 3M/Re s`.
2. Fubini on `0<Re s<1`: `Φ₀(s) = ∫_0^∞ a^{s−1}F(a) da = M[φ_1](s)·W(1−s) = −(η(s)/s) W(1−s)`,
   `W(z) = ∫_0^1 w t^{z−1} dt` (analytic `Re z > 0`, `|W| ≤ M/Re z`).
3. `V(z) = (1−2^{−z})W(z)` on `Re z > 0`; on `Re z < 1`: `V(z) = 2^{−z}·z·(1−z)Φ₀(1−z)/zetaEntire(1−z)`
   (from `η(s) = (1−2^{1−s})ζ(s)`, `(1−2^{−z})/(1−2^{z}) = −2^{−z}`, `ζ(s) = zetaEntire(s)/(s−1)`).
   `zetaEntire` has no zeros on `Re s ≥ 1` (PNT + value 1 at `s=1`) ⟹ `V` entire.
4. Growth (`|t| > 3`): `Re z ≥ δ(t) := A/(log|t|)^9`: `|V| ≤ 2M/δ(t)`; `0 ≥ Re z ≥ −δ(t)` and
   `0 < Re z < δ(t)`: `ZetaInvBnd`; `Re(1−z) ∈ [1+δ,2]`: `ZetaInvBound2`; `Re z ≤ −1`: `|ζ(1−z)| ≥ 2−ζ(2)`.
   So `|V(z)| ≤ C(1+|z|)^N max(1, 2^{−Re z})`.
5. `v = w − w(2·)1_{(0,½]}`: Mellin `V`; `U(z) = 2^z(V(z) − ∫_{½}^1 v t^{z−1})` = `2^z M[v1_{(0,½]}](z)` entire,
   polynomially bounded, `U(x) → 0` (`x→+∞`) ⟹ `U ≡ 0` (Liouville) ⟹ `v = 0` a.e. on `(0,½]` (Fourier uniqueness)
   ⟹ `w(2t) = w(t)` (continuity).
Where `L^p`, `p<∞`, fails: `W` analytic only on `Re z > 1/p`; the strip `0 < Re z ≤ 1/p` needs `1/ζ` bounds on
`1 − 1/p ≤ Re s < 1` — a zero-free half-plane.
