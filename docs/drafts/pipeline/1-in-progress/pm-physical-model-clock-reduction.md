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

## PM-14 (proved, Lean; superseded by PM-15) — bounded witnesses are self-similar
First proof used Zeta23 `ZetaInvBnd`/`ZetaInvBound2`/`ZetaZeroFree` on a thin strip; replaced by PM-15, which needs no
zero-free region. Corollaries kept: `IsFermiNymanWitness.selfSimilar_of_bounded`, `selfSimilar_of_bounded_fermiWitness`.

## PM-15 (proved, Lean) — sharp unconditional boundary: Mellin exponent zero
`RHTower/FermiNymanWitness{Mellin,DyadicDefect,ExponentZeroRigidity}.lean` (build green, axioms standard, wired).
`IsMellinFermiWitness w a`: continuous on `(0,1]`, orthogonal to all `φ_b`, `∫_0^1 t^{x−1}|w| < ∞` for `x > a`.
Theorem `IsMellinFermiWitness.selfSimilar`: exponent `0` ⟹ `w(t/2) = w(t)`. Also `…selfSimilar_of_mellinExponentZero`.
Proof: `W` analytic on `Re z > a` (differentiation under the integral); Fubini on `0<Re s<1−a`; entire `U`;
**growth by maximum modulus on rectangles `[−1,1]×±[T_k,T_{k+1}]` between Titchmarsh IX.7 heights**
(`exists_seq_zeta_inv_horizontal`, corpus) — no zero-free region, no Phragmén–Lindelöf; generic lemma
`exists_polyGrowth_of_zetaInv_bounds`; Liouville along integers `eq_zero_of_polyGrowth_of_tendsto_nat`; Fourier
uniqueness `selfSimilar_of_mellin_lowerDefect`. Sharp: zero witness `t^{ρ̄−1}` has exponent `1−Re ρ > 0`.

## PM-16 (proved, Lean) — the Hermitian identity is exactly RH
`RHTower/FermiNymanWitnessSelfSimilarityCriterion.lean` (build green, axioms standard, wired).
`riemannHypothesis_iff_fermiNymanWitness_selfSimilar : RH ↔ ∀ w, IsFermiNymanWitness w → ∀ t ∈ (0,1], w(t/2)=w(t)`;
**PM-17 [L] the exponent ladder** `zetaZeroFreeStrip_iff_mellinFermiWitness_selfSimilar` (all `a < 1`):
`ζ ≠ 0 on 1−a < Re s < 1  ⟺  every witness of Mellin exponent a with m(x) ≤ B/√(x−a) is self-similar`;
the forward witness is `t^{ρ−1}` (bounded majorant), the converse uses removability on `Re z = a` from the rate.
`…_halfMass` (`∫_0^{½}|w|² = ½∫_0^1|w|²`), `…_halfMass_le` (`q ≥ 0`). Converse proof: L² witness has exponent `½` with
rate `m(½+ε) ≤ (1+‖w‖²)/(2√(2ε))` (AM–GM); under RH `Ξ(1−z) ≠ 0` off `Re z = ½`; at critical zeros the left form has
nonnegative meromorphic order (a pole would beat the `ε^{−1/2}` rate at `z₀+ε`), so the regularized defect is entire;
then PM-15's growth/Liouville/uniqueness with `x₁ = 3/4`. Answer to "is the divisor-selective Hermitian identity
open?": yes, and it is RH itself, formally (both directions in Lean). RH enters only as absence of poles of
`V_w(z) = (1−2^{−z})W(z)` in `Re z < ½`.
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

## PM status (closed)
The route's producer class is Mellin-diagonal (gate KR-R2) and every PM receiver is now an exact Lean equivalence:
RH ⟺ L² witness self-similarity ⟺ half-mass ⟺ `q ≥ 0` (PM-16); zero-free strips ⟺ rigidity at each Mellin exponent
(PM-17); exponent 0 unconditional (PM-15). Positive survivors all formalized. Open cores left outside PM:
MC (Möbius cancellation at the half power) and WL (one-sided prime inequality at scale `√X`; routes 1 and 3 land there).

## PM-18 (proved, Lean) — every off-line zero forces a negative direction of `q`
`RHTower/FermiNymanWitnessNegativeIndex.lean` (build green, axioms standard, wired).
`exists_dyadicForm_neg_orthonormal`: for `n` distinct zeros in `½ < Re s < 1` there are `n` witnesses with
`q(vᵢ, vⱼ) = −δᵢⱼ`, where `vᵢ = wᵢ + Σₗ Xᵢₗ gₗ` and `X = −½(Q+1)B⁻¹`. The mechanism: `q ≡ 0` on the spurious
span (`dyadicForm_spurious_spurious`), and the cross matrix `Bₗⱼ = (2^{−ρⱼ}−½)/(ρⱼ − dₗ)` with
`dₗ = 2πi(l+1)/log 2` is a nonsingular Cauchy matrix (`eq_zero_of_cauchy_sum_eq_zero`, Lagrange).
`encard_rightStripZeros_le_witnessNegIndex`: `#{ζ(ρ)=0, ½<Re ρ<1} ≤ ind₋(q | witness class)` (in `ℕ∞`);
`riemannHypothesis_iff_witnessNegIndex_eq_zero`: RH ⟺ `ind₋ = 0`.
Meaning: the "RH is a signature problem" reading (free-orbit count = negative index) is now realized on the
physical Fermi source, with the integer bounded below exactly by the off-line zero count.
Open (PM-19, conjecture): equality `ind₋ = Σ multiplicities` — needs the Beurling–Lax structure
`W₂ = S₀ ⊕ closure(zero witnesses and their log-derivatives)`. The deformation-obstruction law predicts
the signature is not homotopy-computable from the source alone.
Quantum margin [L]: `riemannHypothesis_iff_witnessNegIndex_le_one` — the index is 0 or ≥ 2 (off-line zeros come in
conjugate pairs; no real zeros in the strip, `riemannZeta_ne_zero_of_abs_im_lt_four`). This is route 3's "K < 2"
structure realized on the physical source; by the gate on sub-quantum margins (KR-R1/R3) the margin is idle.

## PM-19a (proved, Lean) — the RH defect is localized at poles, unconditionally
`IsFermiNymanWitness.selfSimilar_of_removable` / `IsMellinFermiWitness.selfSimilar_of_removable`
(`FermiNymanWitnessSelfSimilarityCriterion`, axioms standard): a continuous L² witness is self-similar as soon as the
left form `−2^{−z}z(1−z)Φ₀(1−z)/Ξ(1−z)` of its conjugate has nonnegative meromorphic order at every zero of
`Ξ(1−z)` in `Re z < ½` — no RH hypothesis. Isolated zeros now come from the identity theorem
(`eventually_zetaEntire_one_sub_ne_zero`); the zero-free ladder is a corollary. So the kernel of the principal-part
map at the points `1 − ρ` (`Re ρ > ½`) is exactly the self-similar class: `dim(W₂/S₀) ≤` total pole order, and with
PM-18, `#zeros ≤ ind₋(q) ≤ dim(W₂/S₀)`. PM-19b's former multiplicity and upper-count obligations are closed below.

## PM-19b (proved, Lean, 2026-09-29) — exact analytic-multiplicity index

`witnessNegIndex_eq_rightStripMultiplicityCount` (`FermiNymanMultiplicityIndex`) proves the
unconditional extended equality. Normalized logarithmic zero jets and confluent spurious duals
give literal `−I_M`, `+I_M`, zero-cross blocks for every finite multiplicity packet. Complex-linear
correlation-Mellin jets give the matching upper bound: a zero packet clears every left-defect pole,
hence forces self-similarity and zero quadratic form; a negative Gram span therefore injects into
the multiplicity target. Finite/infinite zero cases are discharged internally. No simplicity,
finite-zero, RH or positivity premise. Five new leaves wired; targeted builds, direct actual-leaf
audits and axiom audits passed (only `propext`, `Classical.choice`, `Quot.sound`).

E: `FermiNymanLogarithmicWitness`, `FermiNymanConfluentCoupling`,
`FermiNymanMultiplicitySignature`, `FermiNymanCorrelationJets`, `FermiNymanMultiplicityIndex`;
`3-formalized/pm-fermi-multiplicity-hyperbolic-signature.md`.
Open: an independent source bound on this index, witness nonnegative half-mass or Haar-target
approximation. Difference-rank equality and the exact bounded correlation-jet kernel are now
formalized; neither is a source positivity producer.

## PM-20 (proved, Lean, 2026-09-30) — weighted saturation above the critical parameter

The original source constraints with squared-norm weight `t^(2a-1)` and form subtraction
coefficient `2^(-2a)` preserve every spurious neutral mode. A power witness is admitted exactly
when `Re rho>1-a`; its weighted energy is `1/(2(a+Re rho-1))`. Exact spurious coupling translates
the Cauchy nodes to `d_l+1-2a`, so every finite packet of distinct admitted zeros yields `-I_n`.
Unconditional Hardy critical-line zeros therefore give infinite index for all `1/2<a<1`.

`weightedWitnessNegIndex_boundary_profile` has no hypothesis parameters: canonical index
vanishing at `a=1/2` is RH, and all strictly supercritical admissible parameters have infinite
index. No actual jump at the boundary is claimed, since its index remains uncontrolled.
PM-21 below closes full weighted multiplicity equality. Parameter continuity alone supplies
no index bound: mode energy diverges at admission thresholds.

E: `FermiNymanWeightedWitness`, `FermiNymanWeightedSignature`;
`3-formalized/pm-weighted-critical-index-saturation.md`;
`3-formalized/pm-weighted-multiplicity-tomography.md`.
Both targeted old-mode builds and direct actual-leaf audits passed. All 42 new declarations
and the Hardy input use only `propext`, `Classical.choice`, `Quot.sound`; both leaves are wired.

## PM-21 (proved, Lean, 2026-09-30) — exact weighted multiplicity profile

For every `0<a<1`, the literal weighted negative index equals the full analytic-multiplicity
count of actual zeros in `1-a<Re rho<1`, in `ℕ∞`. Weighted correlation jets clear all
left-defect poles and force self-similarity when their packet vanishes; shifted Mellin
transforms give exact normalized logarithmic Cauchy columns and multiplicity-exact signed
blocks. No RH, simplicity or finite-zero premise enters.

E: `FermiNymanWeightedCorrelation`, `FermiNymanWeightedConfluentCoupling`,
`FermiNymanWeightedMultiplicity`; `RHTower.weightedWitnessNegIndex_multiplicity_profile`;
`3-formalized/pm-weighted-multiplicity-tomography.md`.
All targeted old-mode builds and final direct actual-leaf checks passed. All 48 new
declarations use only `propext`, `Classical.choice`, `Quot.sound`; all leaves are wired.
Generated indexes are current; global lint still flags 17 unrelated unwired modules.

The source estimate forcing the canonical index to zero remains open. Next candidate:
`3-formalized/pm-weight-zero-domain-boundary.md`, auditing the endpoint domain and why
its triviality cannot alone justify positive-weight index constancy. The RH goal is active.

## PM-22 (proved, Lean, 2026-09-30) — singular zero-weight source domain

Every source witness at a nonpositive weight vanishes on `(0,1]`; at every positive
weight a nonzero spurious source witness exists. That fixed witness has exact energy
`1/(2a)`, unbounded on every interval `(0,ε)`. Triviality at weight zero therefore supplies
no uniform energy control across the changing domain.

E: `FermiNymanWeightDomainBoundary`; `RHTower.weightedFermiWitness_domain_boundary`;
`3-formalized/pm-weight-zero-domain-boundary.md`. Targeted old-mode build and final actual-leaf
check passed. All eight declarations use only the standard three axioms; leaf wired and
indexes current. Global lint flags 11 unrelated unwired modules.

The subsequent raw-coefficient test is closed below. RH remains open and the user goal remains active.

## PM-23 (proved no-go and positive survivor, Lean, 2026-10-01) — raw Möbius Haar tail floor

The literal approximation `A_N=-Σ_(d≤N) μ(d)φ_d` equals Haar on `1/(N+1)<t≤1`, but its
full squared error is at least `(N+1)H_N²/6`. All error lies on the shrinking complementary
interval, and one strictly positive error floor recurs cofinally. Thus the exact raw sequence
cannot converge in the PM norm. Full-half-line dilation coercivity supplies the continuous
transfer; no discrete norm is substituted.

E: `FermiNymanRawMobiusTailFloor`; `frequent_rawMobiusFermiErrorEnergy_floor`;
`not_tendsto_rawMobiusFermiErrorEnergy_zero`; `5-failed/pm-raw-mobius-haar-tail-floor.md`.
All 24 declarations passed a targeted old-mode build, final direct actual-leaf check, and
axiom audit using only the standard three axioms. Leaf wired; generated indexes current.
Global lint flags 12 unrelated unwired modules, listed on the failed-route card.

Next: `1-in-progress/pm-log-smoothed-mobius-haar.md`. The logarithmically weighted
coefficients have a proposed exact continuous head identity in terms of
`2ψ(1/(2t))-ψ(1/t)`, supported by existing discrete divisor identities. Head/tail mean-square
control remains open. This no-go does not reject all coefficients or settle RH.

## PM-24 (proved exact bridge, Lean, 2026-10-01) — logarithmic Fermi/Chebyshev head

For coefficients `μ(d)log(N/d)/log N`, `N≥2`, the literal Haar error on
`1/(N+1)<t≤1` equals `[2ψ(1/(2t))-ψ(1/t)]/log N`. The full squared error equals
the unchanged small-`t` tail plus the normalized square integral of that exact prime
discrepancy on the head. Measurability and integrability are included.

E: `FermiNymanLogMobiusHead`; `dyadicHaar_sub_logMobiusFermiApprox`;
`logMobiusFermiErrorEnergy_decomposition`; `1-in-progress/pm-log-smoothed-mobius-haar.md`.
All 13 declarations passed targeted old-mode build, final direct leaf and standard-axiom
audits; leaf wired. Canonical convergence remains open. The partial variance search
returns conditional power bounds and an unconditional `e(x)/x²` integrability theorem.

That weighted endpoint is now formalized below. The missing power needed for the
canonical norm remains explicit; RH goal remains active.


## PM-25 (proved weighted source, Lean, 2026-10-01) — logarithmic Möbius convergence in `t dt`

The literal logarithmic Fermi approximation satisfies
`∫_(0,1] t |h-A_N^log|² ≤ (N+1)^(-2)+(C+9)/(log N)² → 0` for a fixed finite
nonnegative arithmetic constant `C`. The source proof establishes `Q²/x³`
integrability from the unconditional PNT error integral and transports it by the
exact reciprocal Jacobian. The linear Barban–Vehov mass bound controls the tail.

E: `ChebyshevDyadicWeightedEnergy`; `FermiNymanLogMobiusWeightedEndpoint`;
`weightedLogMobiusFermiErrorEnergy_le`; `tendsto_weightedLogMobiusFermiErrorEnergy_zero`;
`3-formalized/pm-log-mobius-weighted-endpoint.md`. Both targeted builds and final
actual-leaf checks passed. All 23 declarations use only the standard three axioms;
leaves wired, names/API entries unique, indexes refreshed. Global lint flags only
11 unrelated unwired modules, enumerated on the card.

Canonical `dt` convergence is not proved. Two complete new searches return the
scalar normalization `B_N→1` but no canonical energy rate. The exact auxiliary
variance candidate is now formalized below in
`3-formalized/pm-log-mobius-auxiliary-variance.md`. No critical-line
multiplicity obstruction is asserted without its own proof. RH remains open.


## PM-26 (proved canonical source constraint, Lean, 2026-10-01) — auxiliary prime/Möbius variance

The literal logarithmic auxiliary error satisfies
`E_N(t)=[B_N/t−ψ(1/t)]/log N` for `t>1/(N+1)`. Reciprocal transport gives its exact
tail norm as `V_N/log²N`, where `V_N=∫_(0,N+1)(B_N−ψ(x)/x)² dx`. General finite-
coefficient coercivity proves `V_N/log²N≤6 E_Fermi(N)` in the actual canonical norm.

The exact decomposition
`V_N=(N+1)(B_N−m_N)²+∫_(0,N+1)(m_N−ψ(x)/x)² dx`
separates scalar normalization from intrinsic prime-profile fluctuations. Each
nonnegative term obeys the same canonical-error bound. The existing scalar limit
`B_N→1` does not supply either required critical rate.

E: `FermiNymanFiniteCoefficientError`; `FermiNymanLogMobiusAuxiliaryVariance`;
`logMobiusChebyshevVariance_le_six_error`; `logMobiusChebyshevVariance_decomposition`;
`3-formalized/pm-log-mobius-auxiliary-variance.md`. Two targeted leaves and both final
actual-leaf checks passed. All 31 declarations use only the standard three axioms;
names, imports and API entries checked. Final global lint flags only 12 unrelated
unwired modules, listed on the card. No canonical convergence or RH conclusion.

Four complete source searches supply no independent critical variance upper bound.
That candidate is now audited in `5-failed/pm-weighted-source-input-power-boundary.md`.
It tests precisely the available analytic hypotheses via an explicit monotone power
profile, retaining the sharp optimal-variance classification as its positive
survivor. It makes no counterexample claim about actual primes, Möbius sums or RH.


## PM-27 (analytic-input no-go and positive classification, Lean, 2026-10-01)

The listed analytic PNT inputs admit explicit monotone `x+x^σ` profiles with every
`0<σ<1`. Their optimally centered variance is exactly classified: finite limit for
`σ<1/2`, logarithmic growth at `1/2`, and a positive `R^(2σ−1)` asymptotic above it.
Every scalar centering preserves supercritical divergence after division by log²R.
The unconditional existential obstruction includes both improper integrals from
`1/2` and every stretched-log envelope of exponent below one.

Positive survivor: exact finite moments, unique minimizing mean, full scalar
variance decomposition and sharp asymptotic threshold. All 46 declarations in
`PMAnalyticPowerModel`, `PMAnalyticPowerVariance`, `PMAnalyticPowerBoundary` passed
three targeted builds, three final actual-leaf checks and standard-axiom audits.
Leaves wired and API/index checks passed. Lint finds only 11 unrelated unwired
modules enumerated on `5-failed/pm-weighted-source-input-power-boundary.md`.

Only the analytic-input inference is closed. Actual Möbius/Chebyshev arithmetic and
RH remain open. Two complete further searches, all 40 candidate/source statements
in each reviewed, return the actual Selberg `400N` recursion and chronological
prime-work balance, with no independent critical upper producer. Next card:
`pm-selberg-recursion-power-response.md`.


## PM-28 (coarse Selberg-input boundary, Lean, 2026-10-01)

Actual von Mangoldt weights do not remove the PM-27 comparison obstruction when
only the two existing inequalities, with constants `400`, `800`, `2900`, are
used. The same explicit power profile obeys both yet has divergent canonical
variance for every centering. Positive survivor: exact floor-hyperbola response
`Tσ(N)/N→Sσ`, `1<Sσ≤1/(1−σ)`, and corrected signed response `Sσ−1`. The value
at quotient one affects the entire prime half-interval, not only `Λ(N)`.

Three new leaves / 45 declarations / 541 lines passed targeted builds, three
final actual-leaf checks and every standard-axiom audit. Wiring, unique APIs
and names checked; generated indexes current. Lint flags only 10 unrelated
unwired modules listed on `5-failed/pm-selberg-recursion-power-response.md`.

Next: `pm-selberg-sublinear-response-boundary.md`, whose rescaled comparison
amplitude `1/(2Sσ−1)` is proposed to cancel the linear response while preserving
variance divergence. Actual-source constants remain distinct: existing second-
grade prime asymptotics include `−2γ`. No actual critical estimate or RH proof.


## PM-29 (sublinear response boundary, Lean, 2026-10-01)

The rescaled comparison model has exact normalized signed response
`cSσ−(1+c)/2`. It is sublinear at the unique positive amplitude
`c=1/(2Sσ−1)<1`, while every scalar-centered canonical variance still diverges
for `σ>1/2`. The quantitative variance comparison retains the finite initial
cell; both existing Selberg inequalities hold with unchanged constants.

Two leaves / 32 declarations / 387 lines passed targeted builds, final direct
actual-leaf and all standard-axiom checks. Bodies/names/imports/API audited;
index current; lint only 11 unrelated unwired modules listed on
`5-failed/pm-selberg-sublinear-response-boundary.md`. The exact affine law and
unique cancelling amplitude are the formalized positive survivor.

This does not assert a zero response for the actual unshifted Chebyshev error.
Next actual-source audit: `pm-log-mobius-boundary-multiplicity.md`, testing
whether fixed logarithmic coefficients force critical simplicity as well as RH.
No implication claimed yet; original unconditional RH goal remains active.

## PM-30 ingredient: exact coefficient Mellin pair (2026-10-01)

`PMLogMobiusMellinPair` proves the literal real-cutoff logarithmic Möbius
coefficient transform `1/[s²ζ(s+1)]` on `Re s>0`, with convergence and exact
floor/end-point matching. Its 11 declarations are fully audited. The proposed
fixed-coefficient simplicity implication remains in progress on
`pm-log-mobius-boundary-multiplicity.md`; actual critical variance and RH remain
open. No boundary conclusion follows from this right-half-plane identity alone.

PM-30 completed: six leaves / 64 declarations / 1,196 lines prove that canonical
fixed logarithmic error convergence forces every critical-line zero simple.
The exact source identities, continuous budget, continuation and quadratic Abel
limit are fully audited. Capstone: `pmLogMobius_critical_simple_of_error`.
Card: `3-formalized/pm-log-mobius-boundary-multiplicity.md`. Neither convergence
nor unconditional simplicity nor RH is proved. An alternate approximation must
be audited against this extra boundary requirement before it becomes a producer.

PM-31 source ingredient completed: `PMPowerDampedMobiusSource`, 250 lines / 14
audited declarations, proves pointwise Haar convergence of the literal
power-damped Möbius family, its Chebyshev first derivative and canonical `L²(dt)`
admission for `ε>1/2`. The proposed replacement producer is admission for positive
dampings arbitrarily close to zero; this remains unproved. Exact Mellin and
analytic receiver certification is in progress on `pm-power-damped-mobius-haar.md`.

PM-31 Mellin ingredient also completed: `PMPowerDampedMobiusMellin` adds 200
lines / 14 audited declarations. The literal transform is exactly
`(1−2^(1−s))ζ(s)/(sζ(s+ε))` on its absolute-convergence strip. Explicit canonical
`MemLp` gives absolute Mellin convergence and analyticity on `Re s>1/2`.
Combined PM-31 certificate: fifteen leaves / 3595 lines / 226 declarations.
`PMPowerDampedMobiusCriterion` now proves the pole-cleared continuation and
cofinal-admission RH receiver, with all five declarations fully audited. Under
`¬RH`, a whole interval of small positive dampings fails canonical admission.
The actual small-damping estimate remains open; no unconditional RH claim.

PM-31 prefix-energy ingredient fully audited: `PMPowerDampedMobiusPrefixEnergy`
transfers the existing full modular norm to the literal Fermi source and proves
unconditional `O(N/log(N)^q)` square-energy bounds for every fixed positive
integral order. `PMPowerDampedMobiusEndpoint` now certifies unconditional
admission at `ε=1/2` and hence every `ε≥1/2` (246 lines / 12 declarations).
Targeted build, final actual-leaf, standard-axiom and exhaustive API/body/name/import
audits passed. Arbitrarily small positive damping remains open.

PM-31 exact Gram diagonal fully audited: `PMPowerDampedMobiusGramDiagonal`,
259 lines / 18 declarations. Each generator has squared norm `log(2)/a`;
the damped Möbius diagonal is summable for every positive damping. Positive
blocks disprove every coefficient-independent fixed diagonal ceiling. Actual
Möbius cross-term control and arbitrarily small canonical admission remain open.

PM-31 prime-contraction no-go closed with a positive survivor: canonical
prime cutoffs must sometimes increase norm arbitrarily near zero damping, and
every limiting uniform norm budget is at least one. All 19 new declarations
passed targeted/direct-leaf/standard-axiom and exhaustive source/API audits.
Card: `../5-failed/pm-power-damped-prime-contraction.md`. Finite budgets allowing
this growth and small-positive-damping admission remain open.

PM-31 large-damping asymptotic fully audited: `PMPowerDampedMobiusLargeDamping`
proves `2^ε(E_ε−log 2)→−2κ` with `κ≥1/12`, hence actual canonical norm growth
beyond every damping threshold. The proposed eventual damping monotonicity is
retired with this positive survivor on `5-failed/pm-power-damping-monotonicity.md`.
The unit upper budget and small-positive canonical admission remain open.

PM-31 exact mean fully audited: `PMPowerDampedMobiusMean` (203 lines / 12
declarations) proves canonical L¹ admission at every positive damping, mean
`log 2/ζ(1+ε)`, and mean/ε→log 2. For an admitted L² source, the exact Haar-error
identity is `error²=source²−1+2 Re(mean)`. No unit budget or small-positive L²
admission follows yet. Next: certify the paper-proved canonical L¹ error bound
`||A_ε−Haar||₁≤Cε` from shrinking raw-prefix support and finite Abel sums.

PM-31 canonical L¹ convergence fully audited: `PMPowerDampedMobiusL1Convergence`
(260 lines / 19 declarations) proves `||A_ε−Haar||₁≤Cε`, where the explicit
constant `C=Σ_n ||R_n−Haar||₁/n` is finite. Shrinking raw-prefix support converts
the known L² logarithmic savings to this reciprocal L¹ budget; finite Abel
sums and Fatou transfer it to the literal source. Small-positive L² admission
remains open. Next: the canonical L¹ derivative and its distinct L² boundary.

- PM-31 derivative audit closed: `PMPowerDampedMobiusDerivative` (304 lines /
  29 declarations) passed targeted old build, final actual leaf, every axiom
  report (standard three only), exact body/API/name/unique-import gates.
  The actual difference quotients converge in canonical L¹ to the dyadic
  Chebyshev source, whose signed integral is log 2. Combined: twelve audited
  leaves / 2917 lines / 181 declarations. Small-positive L² admission and RH
  remain open; the derivative's proposed L² exclusion is not yet certified.

- PM-31 Hilbert-tangent obstruction audit closed: two additional leaves,
  `PMPowerDampedMobiusDerivativeMellin` (153/10) and
  `PMPowerDampedMobiusDerivativeBoundary` (226/6), passed targeted builds,
  both final actual leaf checks, every standard-axiom report, exact body,
  exhaustive name, public API and unique-import audits. Combined PM-31:
  fourteen fully audited leaves / 3296 lines / 197 declarations. The exact
  strong L¹ Chebyshev tangent is outside canonical L²; actual quotient norms
  exceed every finite budget arbitrarily near zero. Closed failed card:
  `5-failed/pm-power-damping-hilbert-tangent.md`, retaining the positive L¹
  convergence and exact mean log 2. Small-positive L² admission and RH remain
  open. Next: exact prime-two-deleted Haar resolvent and the all-subset unit
  ceiling, tracked in `pm-dyadic-prime-deletion-unit-budget.md`.

- Dyadic resolvent ingredient fully audited: `PMPowerDampedMobiusDyadicResolvent`
  (299 lines / 29 declarations), targeted old build 18s, final actual leaf empty,
  all standard-axiom/body/name/API/unique-import gates passed. Exact canonical
  energy 2, mean 0, norm sqrt 2 and pointwise support/recurrence uniqueness are
  certified. Combined PM-31: fifteen leaves / 3595 lines / 226 declarations.
  Odd-Möbius identification and all-subset budget obstruction remain pending;
  no closure of the prime-deletion no-go yet. Small-positive L² admission and
  RH remain open. Latest lint: twelve unrelated unwired modules and concurrent
  LEAN_API staleness; no owned or proof-debt finding.

- PM-31 prime-two deletion audit closed: `PMPowerDampedMobiusDyadicDeletion`
  (257 lines / 26 declarations), targeted old build 7.3s, final actual leaf
  empty, all bodies/names/API/unique-import/standard-axiom gates passed.
  The literal odd-Mobius source equals the Haar resolvent: canonical L2,
  exact energy 2, mean 0, norm sqrt 2. Every finite-prime all-subset budget
  below sqrt 2 fails arbitrarily near zero damping, with admitted actual
  finite sources as witnesses. Moved `pm-dyadic-prime-deletion-unit-budget`
  to `5-failed`, preserving the fully proved positive survivor. Combined:
  sixteen leaves / 3852 lines / 252 audited declarations. Latest global lint:
  twelve unrelated unwired modules; no owned or proof-debt finding.
  Next conjecture: `pm-finite-prime-deletion-energy` tests whether every
  finite all-subset budget fails via the nonnegative Haar Gram kernel and
  smooth-number harmonic energy. Canonical full cutoffs and RH remain open.

- PM-31 Haar Gram leaf fully audited: `PMPowerDampedMobiusHaarGram`
  (211 lines / 26 declarations), targeted old build 152s, final actual leaf
  empty, all exact-body/name/API/unique-import/standard-axiom gates passed.
  It proves K(a,b)=max(0,2/max(a,b)-1/min(a,b)), finite Haar-sum energy,
  diagonal lower bounds and energy monotonicity under finite inclusion.
  Combined PM-31: seventeen leaves / 4063 lines / 278 audited declarations.
  Latest lint: thirteen unrelated unwired modules; no owned/proof-debt finding.
  Hilbert-series scratch1045 is checking; smooth-source scratch1046 is
  prepared but unrun. The stronger all-subset budget no-go is not closed.
  Canonical small-positive admission and RH remain open.

- PM-31 Hilbert-series leaf fully audited: `PMPowerDampedMobiusHaarSeries`
  (151 lines / 16 declarations), targeted old build 92s, final actual leaf
  empty, all exact-body/name/API/unique-import/standard-axiom gates passed.
  Summable dilation norms identify the actual pointwise series with its
  Hilbert sum; exact energy is the iterated Gram sum and dominates every
  finite reciprocal diagonal. Combined: eighteen leaves / 4214 lines /
  294 audited declarations. Latest global lint: seventeen unrelated unwired
  modules and three concurrently stale generated files; no owned or proof-debt
  finding. Sixteen-declaration smooth-source scratch1046 checks next;
  nine-declaration arithmetic scratch1047 is prepared and unrun. The broader
  no-go and canonical small-positive admission/RH remain open.

- PM-31 smooth-source leaf fully audited: `PMPowerDampedMobiusSmoothHaar`
  (147 lines / 16 declarations), targeted old build 4.6s, final actual leaf
  empty, all exact-body/name/API/unique-import/standard-axiom gates passed.
  Each fixed smooth-number Haar source is canonically L2/L1, supported in
  (0,1], with zero mean and exact nonnegative Gram energy. Its energy
  dominates the harmonic sum and diverges with the prime cutoff. Combined:
  nineteen leaves / 4361 lines / 310 audited declarations. Latest global
  lint: ten unrelated unwired modules and three concurrent generated-file
  changes; no owned/proof-debt finding. Full 23-declaration arithmetic/budget
  scratch1047 checks next. The broader all-subset no-go is not closed yet.
  A separate paper candidate `pm-canonical-prime-aperture-threshold` tests
  divergence at fixed epsilon<1/2 even for canonical prime cutoffs, paired
  with explicit all-subset bounds for epsilon>1/2. No Lean proof of that
  stronger candidate is claimed. Actual small-positive admission/RH stay open.

- PM-31 arithmetic/deletion leaf fully audited: `PMPowerDampedMobiusFiniteDeletion`
  (283 lines / 23 declarations), targeted old build115s, final actual leaf empty,
  every exact-body/name/API/unique-import/standard-axiom gate passed. Literal
  deleted Mobius sources equal smooth Haar sums. For every finite budget and
  every positive damping neighborhood, an admitted actual finite prime source
  exceeds that budget. Combined: twenty leaves / 4644 lines / 333 declarations.
  Global lint: eleven unrelated unwired modules and three concurrently stale
  generated files; no owned/proof-debt finding. The strongest arbitrary-finite-set
  positive survivor is prepared in scratch1050 (22 declarations), now checking.
  No-go closure awaits that exact generality; actual small-positive admission
  and unconditional RH remain open.

- PM-31 arbitrary finite-deletion survivor fully audited:
  `PMPowerDampedMobiusFiniteSmoothSource` (220 lines / 22 declarations), targeted
  old build7.7s, final actual leaf empty, all exact-body/name/API/unique-import/
  standard-axiom gates passed. For every finite E, the literal deleted-Mobius
  source equals its strongly summable smooth Haar series, is canonically L2/L1,
  has zero mean and exact nonnegative double-Gram energy, with reciprocal Euler
  product diagonal lower bound. Combined: twenty-one leaves / 4864 lines /
  355 audited declarations. Global lint: thirteen unrelated unwired modules
  and two concurrently stale generated files; no owned/proof-debt finding.
  Retired `pm-finite-prime-deletion-energy`: every finite all-subset bound
  uniform in damping near zero is impossible, with the exact arbitrary-finite-E
  positive survivor now on paper and in Lean. This does not exclude a finite
  C(epsilon), canonical-only bounds, or actual small-positive admission.
  Next candidate: `pm-canonical-prime-aperture-threshold`; scratch1051 checks
  the upper boundary and real Euler decay, while1053/1055 remain unrun.
  Unconditional RH/negRH remain unproved.

- PM-31 canonical prime threshold fully audited: `PMPowerDampedMobiusPrimeThreshold`
  (436 lines / 22 declarations), targeted old build197s, final actual leaf empty,
  all exact-body/name/API/unique-import/standard-axiom gates passed. For every
  fixed0<epsilon<1/2, canonical prime-aperture norms tend to infinity and
  eventually exceed every finite budget. The exact positive survivor is the
  explicit common finite budget `3 sum_d d^(-epsilon-1/2)` for epsilon>1/2,
  valid for every finite integer aperture, together with the proved finite
  Mellin identity and bounded-cofinal Mellin transfer. Endpoint1/2 unclassified.
  Combined: twenty-two leaves /5300 lines /377 audited declarations. Latest
  global lint: eleven unrelated unwired modules and two concurrently stale
  generated files; no owned/proof-debt finding. Retired canonical prime-budget
  producer with the strict-interval classification fully proved on paper and
  in Lean. Actual source admission at arbitrarily small positive damping and
  unconditional RH/negRH remain open. Next card:
  `pm-centered-divisor-haar-criterion`, an exact mean-centered discrepancy
  energy criterion with paper argument and corpus audit; no new Lean yet.

- PM-31 centered-divisor arithmetic leaf fully audited:
  `PMPowerDampedMobiusDivisorHaar` (295 lines /29 declarations), targeted old
  build24s, final actual leaf empty, all exact-body/name/API/unique-import/
  standard-axiom gates passed. Positive divisor coefficients have exact
  Euler factors; their summatory mean is `1/zeta(1+epsilon)`. The actual
  Fermi source is both a finite weighted Haar sum and the dyadic difference
  of its mean-centered reciprocal summatory remainder. The backward boundary
  vanishes and the finite dyadic sums converge pointwise to that literal
  centered source. Combined: twenty-three leaves /5595 lines /406 audited
  declarations. Global lint has ten unrelated unwired modules and three
  concurrently stale generated files; no owned/proof-debt finding.
  Scratch1063 now checks reverse L2 admission with constant `1+sqrt2`,
  forward admission, and reciprocal weighted-energy equivalence. The actual
  small-positive arithmetic energy bound remains open; RH/negRH unproved.

- PM-31 centered-energy criterion fully audited:
  `PMPowerDampedMobiusCenteredEnergy` (226 lines /22 declarations), targeted
  old build119s, final actual leaf empty, all exact-body/name/API/unique-import/
  standard-axiom gates passed. For epsilon>0, actual Fermi-source canonical
  L2 admission is equivalent to integrability of the literal centered divisor
  discrepancy squared against dx/x^2. Backward finite-sum norms have the
  explicit bound (1+sqrt2) times the source norm; Fatou identifies the actual
  boundary-normalized remainder. The reciprocal energy identity, inherited
  epsilon>=1/2 admission, and cofinal weighted-energy RH receiver are proved.
  Combined: twenty-four leaves /5821 lines /428 audited declarations.
  Global lint has eleven unrelated unwired modules and three concurrently
  stale generated files; no owned/proof-debt finding. The energy receiver's
  small-positive premise remains open. New producer card:
  `pm-centered-divisor-dyadic-energy-budget`; scratch1068 checks the exact
  pointwise absolutely summable damped Nyman/fractional-part representation.
  No RH/negRH proof or small-positive geometric energy bound is claimed.

- PM-31 literal Nyman-series leaf fully audited:
  `PMPowerDampedMobiusNymanSeries` (95 lines /11 declarations), targeted old
  build34s, final actual leaf empty, every exact-body/name/API/unique-import/
  standard-axiom gate passed. The centered discrepancy is the negative
  damped fractional-part series, pointwise absolutely summable at every
  positive damping and positive physical time. Its natural integer prefixes
  converge pointwise to the actual centered source; the density is real.
  Combined: twenty-five leaves /5916 lines /439 audited declarations.
  Global lint: eleven unrelated unwired modules and three concurrently stale
  generated files; no owned/proof-debt finding. The actual small-positive
  dyadic/cumulative energy bound remains open. Next: exact unrestricted
  discrete weighted-energy/covariance bridge, then the signed arithmetic
  bound. No global L2 interchange or RH/negRH proof is asserted.

- PM-31 unrestricted discrete-energy leaf fully audited:
  `PMPowerDampedMobiusDiscreteEnergy` (224 lines /18 declarations), targeted
  old build143s, final actual leaf empty, every exact-body/name/API/unique-
  import/standard-axiom gate passed. Unit-cell integrability and countable
  assembly remove the old bounded-sequence premise. For every epsilon>0,
  actual canonical admission is equivalent to summability of
  D_epsilon(n)^2/(n(n+1)), where D is the cumulative centered divisor
  coefficient. Equivalently, its exact finite signed maximum-index
  covariance has a common bound in the cutoff. The epsilon>=1/2 range is
  unconditional; cofinal small-positive budgets would imply RH but remain
  unproved. Combined: twenty-six leaves /6140 lines /457 audited declarations.
  Global lint reports eleven unrelated unreachable modules; no owned or
  proof-debt finding. No RH/negRH proof is claimed.

- PM-31 positive-divisor Haar prefix leaf fully audited:
  `PMPowerDampedMobiusPositiveHaarPrefix` (239 lines /21 declarations),
  targeted old build64s, final actual leaf empty, all exact-body/name/API/
  unique-import/proof-debt/standard-axiom gates passed. The exact clipped
  counts give stabilization to the actual source and the initial plateau
  -C_epsilon(N), with energy contribution C_epsilon(N)^2/(2N). Rescaled
  prefixes converge pointwise to alpha_epsilon times the universal boundary
  profile beta, with common 3min(1,1/u) envelope. Each finite prefix has zero
  integral. Combined: twenty-seven leaves /6379 lines /478 declarations.
  Strong L2 profile/leading energy is checking in scratch1080; do not retire
  this cutoff candidate until that positive survivor is fully audited.
  Actual small-positive source admission and RH remain open. Global lint:
  eleven unrelated unwired modules and concurrent generated-document
  staleness, no owned or proof-debt finding.

- PM-31 universal boundary profile fully audited: `PMPowerDampedMobiusHaarBoundaryProfile`
  (292 lines /19 declarations), targeted old build46s, final actual leaf
  empty, all exact-body/name/API/unique-import/proof-debt/standard-axiom
  gates passed. Rescaled raw positive-Haar prefixes converge strongly in
  L2 to alpha_epsilon*beta; integral beta^2=2-2log2 and integral beta=-log2.
  Their energy divided by the cutoff tends to the strictly positive
  |alpha_epsilon|^2*(2-2log2), so raw-prefix common budgets fail at EVERY
  positive damping. Their L1 error is at least |alpha_epsilon*log2|.
  This does not refute actual-source admission. The exact positive survivor
  closes this no-go; the raw cutoff card is retired. Combined: twenty-eight
  leaves /6671 lines /497 audited declarations. Follow-up: centered Haar
  cutoff/endpoint-trace criterion; the small-positive signed energy
  producer and RH remain open. Global lint: eleven unrelated unwired
  leaves and concurrently stale generated docs, no owned/proof-debt finding.

- PM-31 clipped Haar source fully audited: `PMPowerDampedMobiusClippedHaarSource`
  (242 lines /22 declarations), targeted old build49s, final actual leaf
  empty, all exact-body/name/API/unique-import/proof-debt/standard-axiom
  gates passed. Subtracting alpha_epsilon*N*beta(Nt) gives exactly the
  dyadic difference of R_epsilon(min(N,1/t)); every finite corrected
  prefix is admitted and stabilizes pointwise to the actual source.
  Its primitive energy is exactly truncated divisor energy plus
  |R_epsilon(N)|^2/N. Generic dyadic difference norms lie between
  (sqrt2-1)||f|| and (sqrt2+1)||f||. Combined: twenty-nine leaves /6913
  lines /519 audited declarations. The endpoint convergence and cofinal
  selection proofs are in scratch, not yet certified. Small-positive
  arithmetic admission remains open. Global lint: ten unrelated unwired
  modules and stale LEAN_GAPS/LEAN_OVERVIEW, no owned/proof-debt finding.

- PM-31 cutoff trace/cofinal criterion fully audited:
  `PMPowerDampedMobiusHaarCutoffTrace` (324 lines /16 declarations),
  targeted old build15s, final actual leaf empty, all exact-body/name/API/
  unique-import/proof-debt/standard-axiom gates passed. Under actual
  admission, both clipped-primitive and density-repaired-prefix L2
  convergence are equivalent to |R_epsilon(N)|^2/N tending to zero.
  Actual admission supplies a strict cofinal trace-zero sequence, and is
  equivalent to a common cofinal repaired-prefix norm budget. The exact
  criterion card moves to formalized. Combined: thirty leaves /7237 lines
  /535 audited declarations. Full-sequence endpoint-atom correction is
  the next paper-proved conjecture; actual small-positive energy admission
  and RH remain open. Global lint: ten unrelated unwired leaves, all three
  generated docs concurrently stale, no owned/proof-debt finding.

- Endpoint correction fully audited: `PMPowerDampedMobiusEndpointHaar`
  (215 lines /17 declarations), targeted old build294s, final actual-leaf
  check with empty diagnostics, all17 standard-axiom reports, exact body,
  exhaustive names/API, unique import and proof-debt checks passed. Its
  exact truncated-source identity removes the endpoint trace, giving
  full-integer-cutoff L2 convergence under actual admission and an exact
  full-sequence energy-budget criterion. Global lint still reports twelve
  unrelated unwired leaves, no owned/proof-debt issue. Combined: thirty-one
  leaves /7452 lines /552 audited declarations. The actual small-positive
  signed energy bound remains open. Next: divisor second-moment density.

- Second-moment density fully audited: `PMPowerDampedMobiusSecondMoment`
  (268 lines /18 declarations), targeted old build36s, final actual-leaf
  check with empty diagnostics, all18 standard-axiom reports, exact body,
  exhaustive names/API, unique import and no-proof-debt checks passed.
  It proves the literal coefficient square's summatory mean and Euler
  product, the centered mean-square gamma-alpha^2>=0, and gamma<=alpha.
  Combined: thirty-two leaves /7720 lines /570 audited declarations.
  Strict positivity, small-damping variance and the logarithmic signed
  covariance calibration remain on the second-moment card. The actual
  small-positive cumulative-energy bound and RH remain open. Global lint
  has eleven unrelated unwired leaves and three generated freshness
  findings; no owned or proof-debt finding, no global pass claimed.

- Signed covariance calibration fully audited:
  `PMPowerDampedMobiusCovarianceCancellation` (269 lines /17 declarations),
  targeted old build7.8s, final actual-leaf check with empty diagnostics,
  all17 standard-axiom reports, exact body, exhaustive names/API, unique
  import and no-proof-debt checks passed. The variance is strictly positive
  at every positive damping. The actual centered diagonal/log N tends to
  this variance and has no common finite budget, including the admitted
  safe range. The exact off-diagonal/log N tends to its negative under
  actual admission, unconditionally at epsilon>=1/2. Combined: thirty-three
  leaves /7989 lines /587 audited declarations. Small-damping variance
  asymptotic is drafted; the canonical small-positive energy bound and RH
  remain open. Global lint has twelve unrelated unwired leaves and stale
  API/overview, no owned/proof-debt finding; no global pass claimed.

- Small-damping variance refinement fully audited:
  `PMPowerDampedMobiusSmallDampingVariance` (251 lines /17 declarations),
  targeted old build76s, final actual-leaf check with empty diagnostics,
  all17 standard-axiom reports, exact body, exhaustive names/API, unique
  import and no-proof-debt checks passed. The exact Euler correction
  tends to one; gamma_epsilon/epsilon and v_epsilon/epsilon both tend to
  1/2 as epsilon->0+. All pole identities use positive damping.
  Combined: thirty-four leaves /8240 lines /604 audited declarations.
  The coefficient second-moment card is now formalized; the actual
  small-positive cumulative-energy bound and RH remain open. Global lint
  reports ten unrelated unwired leaves, no generated freshness error and
  no owned/proof-debt finding; no global pass claimed. Next candidate:
  natural-denominator Ramanujan expansion and its anchored energy budget.

- Actual Ramanujan expansion fully audited:
  `PMPowerDampedMobiusRamanujanExpansion` (245 lines /21 declarations),
  targeted old build37s, final actual-leaf check with empty diagnostics,
  all21 standard-axiom reports, exact body, exhaustive names/API, unique
  import and no-proof-debt checks passed. The literal coefficient has an
  absolutely convergent Ramanujan expansion; centered natural-denominator
  prefixes converge, as do every fixed cumulative sum and finite energy.
  A common cutoff-energy budget would give actual PM admission, but that
  budget remains unproved. Combined: thirty-five leaves /8485 lines /625
  audited declarations. Global lint reports eleven unrelated unwired
  leaves and stale API/overview, no owned/proof-debt finding; no global
  pass claimed. The explicit multiple-weight Euler formula has a paper
  proof and a draft Lean proof, not yet checked. RH remains open.

- Actual Ramanujan weights fully audited:
  `PMPowerDampedMobiusRamanujanWeights` (230 lines /17 declarations),
  targeted old build160s, final actual-leaf check with empty diagnostics,
  all17 standard-axiom reports, exact-body/exhaustive names/API/unique
  import/no-proof-debt checks passed. The coefficient is exactly
  alpha*mu(q)/product_(p|q)(p^(1+epsilon)-1), is real with Mobius-aligned
  sign, and has total absolute mass one. These are unconditional for
  every positive damping, including nonsquarefree vanishing and q=0.
  Combined: thirty-six leaves /8715 lines /642 audited declarations.
  Global lint reports twelve unrelated unwired leaves, no owned or
  proof-debt finding; no global pass claimed. The finite cofactor rewrite
  is checking next. No small-positive anchored energy budget or RH proof.

- Actual Ramanujan cofactors fully audited:
  `PMPowerDampedMobiusRamanujanCofactors` (286 lines /18 declarations),
  targeted old build49s, final actual-leaf check with empty diagnostics,
  all18 standard-axiom reports, exact-body/exhaustive names/API/unique
  import/no-proof-debt checks passed. Natural-denominator cumulative
  prefixes are exactly finite cofactor-weighted fractional-part sums,
  with exact density cancellation. Absolute multiples inversion gives
  the exact mass on squarefree multiples; cofactors preserve Mobius
  signs and have norm at most d^(-epsilon). Combined: thirty-seven
  leaves /9001 lines /660 audited declarations. Global lint has ten
  unrelated unwired leaves and no owned/proof-debt finding; no global
  pass claimed. A proposed logarithmic coefficient-square comparison
  remains unproved; its summable coefficient side is being checked.
  No small-positive anchored energy budget or RH proof.

- Actual Ramanujan logarithmic square mass fully audited:
  `PMPowerDampedMobiusRamanujanLogMass` (59 lines /5 declarations),
  targeted old build47s, final actual leaf empty, all5 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Pointwise |a(q)|<=q^(-1-epsilon); the proposed
  logarithmic square mass is dominated by
  (2^epsilon/epsilon)*q^(-1-epsilon), hence summable for every positive
  damping. Combined: thirty-eight leaves /9060 lines /665 audited
  declarations. Global lint has eleven unrelated unwired leaves, no
  owned/proof-debt finding; no global pass claimed. The energy
  comparison remains unproved. The actual primitive-period mean is
  the next check; no small-positive energy bound or RH proof.

- Actual Ramanujan primitive fully audited:
  `PMPowerDampedMobiusRamanujanPrimitive` (206 lines /18 declarations),
  targeted old build37s, final actual leaf empty, all18 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. The primitive is periodic and bounded for q>1. Its
  exact period mean is -phi(q)/2, also its Cesaro and logarithmic
  harmonic limits. Combined: thirty-nine leaves /9266 lines /683
  audited declarations. Global lint has twelve unrelated unwired
  leaves, no owned/proof-debt finding; no global pass claimed. The
  fixed-q prime Gram asymptotic is checking next. No common cutoff
  energy comparison, small-positive admission or RH proof.

- Actual primitive Gram fully audited:
  `PMPowerDampedMobiusRamanujanGram` (188 lines /13 declarations),
  targeted old build9.9s, final actual leaf empty, all13 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Every fixed pair is absolutely summable; for fixed
  q>1, K(p,q)/log(p)->phi(q)/2 along primes. The exact harmonic head
  has a tail error bounded by the finite-period primitive norm bound.
  Combined: forty leaves /9454 lines /696 audited declarations.
  Lint1129 has fourteen unrelated unwired modules and two shared
  generated-file staleness findings after concurrent changes; no owned
  or proof-debt finding and no global pass claimed. Finite signed Gram
  reduction draft1128 is next; common quadratic bound, small-positive
  admission and RH remain unproved.

- Actual finite signed Ramanujan quadratic fully audited:
  `PMPowerDampedMobiusRamanujanQuadratic` (107 lines /12 declarations),
  targeted old build238s, final actual leaf empty, all12 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Each fixed natural denominator cutoff has finite
  total energy equal to its exact signed primitive Gram quadratic.
  The common Q,T energy budget is equivalent to a common Q bound
  on those literal quadratic forms. Combined: forty-one leaves
  /9561 lines /708 audited declarations. Lint1132 has ten unrelated
  unwired modules and three shared generated-file staleness findings;
  no owned/proof-debt finding and no global pass claimed.
  First-moment/centering draft1133 is checking. Uniform quadratic
  upper bound, small-positive admission and RH remain unproved.

- Actual primitive reciprocal first moment fully audited:
  `PMPowerDampedMobiusRamanujanMoment` (200 lines /17 declarations),
  targeted old build43s, final actual leaf empty, all17 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. The primitive first moment under reciprocal energy
  weights is exactly -Lambda(q), and their mass is1. Period centering
  yields the explicit totient/Lambda correction; energy centering
  R_q+Lambda(q) has weighted mean0 and splits K into Lambda(p)*Lambda(q)
  plus its centered Gram. Combined: forty-two leaves /9761 lines /725
  audited declarations. Lint1135 has eleven unrelated unwired modules
  and two shared generated-file staleness findings; no owned/proof-debt
  finding and no global pass claimed. Actual finite variance reduction
  and centered mixed-Gram law draft1136 are checking. No uniform actual
  variance bound, small-positive admission or RH proof.

- Actual finite energy-centered variance fully audited:
  `PMPowerDampedMobiusRamanujanVariance` (129 lines /12 declarations),
  targeted old build43s, final actual leaf empty, all12 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Actual weighted mean M has a common finite bound at
  each positive damping; G=M^2+V with V>=0, and common Gram/variance
  budgets are equivalent. Centered prime Gram/log(p) tends to
  phi(q)/2-Lambda(q), so logarithmic cross terms survive centering.
  Combined: forty-three leaves /9890 lines /737 audited declarations.
  Lint1139 has twelve unrelated unwired modules and two shared
  generated-file staleness findings; no owned/proof-debt finding and
  no global pass claimed. Absolute natural-cutoff control for damping
  above1/2 is checking in draft1140. Uniform small-positive variance
  upper bound, admission and RH remain unproved.

- Strict absolute natural-denominator budget fully audited:
  `PMPowerDampedMobiusRamanujanAbsolute` (111 lines /7 declarations),
  targeted old build103s, final actual leaf empty, all7 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Common Q,T energy, Gram and centered-variance bounds
  hold for epsilon>1/2 by the exact cofactor fractional-part bound and
  two convergent power sums. No assertion at epsilon<=1/2.
  Combined: forty-four leaves /10001 lines /744 audited declarations.
  Lint1144 has ten unrelated unwired modules; no owned/proof-debt
  finding and no global pass claimed. Endpoint transfer via finite
  Dirichlet convolution remains a paper candidate. Small-positive
  admission and RH remain unproved.

- Exact finite Ramanujan-to-Mobius prefix transfer fully audited:
  `PMPowerDampedMobiusRamanujanTransfer` (132 lines /14 declarations),
  targeted old build55s, final actual leaf empty, all14 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Cofactor Fermi prefix equals the triangular sum of
  actual dilated Mobius prefixes with the explicit convolution kernel;
  no norm bound inferred before the kernel-mass audit.
  Combined: forty-five leaves /10133 lines /758 audited declarations.
  Lint1150 has ten unrelated unwired modules and three shared generated
  file staleness findings; no owned/proof-debt finding, no global pass.
  Kernel prime-factor formula is checking in draft1149. Endpoint and
  small-positive natural-cutoff budgets remain open; RH unproved.

- Exact transfer kernel prime-factor/norm formula fully audited:
  `PMPowerDampedMobiusRamanujanKernel` (196 lines /14 declarations),
  targeted old build62s, final actual leaf empty, all14 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. The norm kernel equals |A(m)|*r^(-epsilon) times
  product_(p|r)(if p|m then 1 else 1/(p^(1+epsilon)-1)); the finite
  product lies in [0,1]. No squarefree premise on m is needed.
  Combined: forty-six leaves /10329 lines /772 audited declarations.
  Lint1156 has ten unrelated unwired modules and three shared generated
  file staleness findings; no owned/proof-debt finding, no global pass.
  Combined mass/Euler/budget draft1157 is checking. Uniform transfer
  norm and endpoint natural-cutoff energy remain unproved; RH unproved.

## 2026-10-17 producer loop (Fable), session goal: overcome a hard obstacle on PM without a bound/receiver
Corpus audit first (all FermiNyman*/PM*/FZZ*/ThetaCuspHawkingBM* docstrings): the physical layers reduce to the
alternating Nyman–Beurling system; PM is unconditionally exactly the NB ladder of zero-free half-planes
(witness exponent a ⟺ ζ≠0 on 1−a<Re s<1; approximation weight t^{2a−1} ⟺ ζ≠0 on Re s>a by the floor;
L^p ⟺ Re s>1/p). Unconditional rung = PNT (exponent 0, weight t dt, L¹ power-damped) — all in the corpus.
Conjectures tested and killed (walls named):
- C1 arithmetic Dirichlet-series operators on the witness class: ‖T_n‖=√n, evaluations land at Re s≤0; no arithmetic
  enters W through bounded operators (Walls 12/14).
- C2 joint dyadic+triadic witness class W_2∩W_3: spurious-free, equals classical NB class (Beurling–Lax); pure receiver.
- C3 heavier Mellin weights to let the mollifier regime dominate: for dt/|t|^{1+δ} point evaluation at off-line
  zeros stays bounded (RH-equivalent, Möbius-sum regime dominates); at δ=0 every Dirichlet polynomial has infinite
  functional (Montgomery–Vaughan growth). Wall 1.
- C4 PM-2 non-attained regime: aliasing natural boundary, sparse approximate dyadic combs are generic (PM-8). No input.
- C5 functional-equation duality for the correlation transform Φ₀^w: vanishing at left-strip zeros is the trivial
  Fubini identity; s↦1−s is t↦1/t which leaves (0,1]; no internal reality structure (Wall 15).
- C6 FE-covariant regularization: the dyadic factor is not FE-covariant; an FE-covariant Dirichlet regularizer
  would have to be almost periodic and decaying — impossible; the sawtooth (NB) is FE-covariant but spurious-free.
- C7 rigidity at exponent a>0 from Vinogradov–Korobov: ladder is an equivalence with a fixed-width zero-free strip;
  only log-refinements of the majorant class are available (excluded as estimates).
- C8 sign certificate for q(w)=−½∫h|w|² on W: pointwise cone vs model-space cone (Wall 13), certificate = spectral
  measure (Wall 12).
Verdict: no producer below a zero-free half-plane exists on PM; the single remaining obstacle is Wall 1 (= RH).
Positive survivor built this session (Lean): the Haar criterion is an exact equivalence, RH ⟺ dyadic Haar
approximable, via a new dilation-average mollifier turning every L² witness into a continuous witness
(so every rigidity theorem for continuous witnesses extends to measurable L² witnesses unconditionally),
h ⟂ every self-similar function, and Hilbert duality closure(span φ_a) = (L² witnesses)^⊥.
Module: RHTower/FermiNymanHaarApproximationEquivalence.lean (status recorded below when built).

## PM-18 (proved, Lean) — the Haar criterion is exactly RH; dilation-average mollifier
`RHTower/FermiNymanHaarApproximationEquivalence.lean` (896 lines; build green, axioms
`propext, Classical.choice, Quot.sound`; umbrella-wired; lint clean for this module).
- `riemannHypothesis_iff_dyadicHaar_approximable`: RH ⟺ ∀ε>0 ∃ finite `Σ c_j φ_{a_j}` (a_j ≥ 1) with
  `∫_0^1 |h − Σ c_j φ_{a_j}|² < ε`. New direction ⟹ (`dyadicHaar_approximable_of_riemannHypothesis`).
- `IsL2FermiWitness` (measurable, square-integrable, orthogonal to all `φ_a`; no continuity).
  `IsL2FermiWitness.dilationAverage_isFermiNymanWitness`: `w_δ = δ⁻¹∫_1^{1+δ} w(·/μ)dμ` is a continuous
  witness for every δ>0 (unconditional). Pieces: general dilation invariance `IsFermiNymanWitness.dilate`
  (all μ ≥ 1), Fubini pairing `integral_mul_conj_dilationAverage`, inversion substitution
  `integral_Icc_comp_div_eq_primitive` (`w_δ(t) = δ⁻¹ t ∫_{t/(1+δ)}^t w(u)u⁻²du`), continuity, and a
  lintegral Cauchy–Schwarz energy bound.
- `integral_dyadicHaar_mul_conj_of_selfSimilar`: `h ⟂` every integrable self-similar function.
- `integral_dyadicHaar_mul_conj_eq_zero_of_riemannHypothesis`: under RH `h ⟂` every L² witness
  (dominated convergence in the dilation parameter, `tendsto_integral_dyadicHaar_mul_conj_comp_div`).
- `dyadicHaarLp_mem_closure_fermiGenSpan`: Hilbert duality `closure span{φ_a} = (L² witnesses)^⊥`.
Meaning: the PM producer target is exactly RH (unlike the fixed log-Möbius family, whose canonical
convergence forces critical simplicity). The mollifier transports every continuous-witness rigidity
theorem of the lane to measurable witnesses. Producer status unchanged: Wall 1.

## 2026-10-17 producer loop, round 2 (Fable)

Scope fixed by the corpus: both PM sides reduce to zero-free half-planes. FZZ side: the two-parameter
family (weight `t^{2a-1}`, damping `ε`) of the power-damped Möbius source is admitted exactly on the
PNT line `a + ε ≥ 1`; every interior point `(a, ε)` is the zero-free half-plane `Re s > a + ε`
(Mellin side: `η(s)/(s ζ(s+ε)) ∈ H²(Re s > a)`); at `a = 1/2` the finite approximants are mollified
second moments with mollifier length `N = T^{1/(1-2ε)}`, beyond every Levinson range (Wall 1).

| cycle | conjecture | verdict |
|---|---|---|
| C9 | spectral calculus of the dilation average `A_δ` on the witness class (acts diagonally on power witnesses; Livšic–Moeller spectrum of the compressed dilation semigroup) | Wall 12: an exact spectral realisation of the off-line zeros, no producer |
| C10 | ergodic dilation average `(log M)^{-1}∫_1^M D_μ w dμ/μ` kills every spurious mode and amplifies zero witnesses by `M^{1-Re ρ}/log M` | receiver: RH ⟺ bounded ergodic averages on witnesses |
| C11 | totality: `{φ_a}_{a≥1} ∪ {t^{-2πik/log 2}}_{k≠0}` dense in `L²(0,1]` | receiver, dual of PM-18 (`W ∩ W_spur^⊥ = 0 ⟺ RH`) |
| C12 | an interior point of the `(a, ε)` ladder below the PNT line | each is `ZFR(a+ε)`, no intermediate rung; mollifier length exponent `1/(1-2ε) > 1` |
| C13 | integer dilations suffice unconditionally: `cl span{φ_n : n ∈ ℕ} = cl span{φ_a : a ≥ 1}` | no unconditional proof: Dirichlet-polynomial closure in `H²(Re s>1/2)` is not the dilation closure; Báez-Duarte's integer criterion uses RH; status open, not a producer |
| PW-B | pure-Ξ no-collision (angular source `≠ 0` at some strict-right zero copy): factors `xi(5ρ/2-1)`, `xi(ρ/2)`, `xi(3ρ/2)` | `3ρ/2` is controlled by a zero of maximal real part, `5ρ/2-1` by the same when `sup Re ρ > 2/3`, `ρ/2` by minimal height; no potential decreases along all three edges; the configuration `Z = {3/5 ± iγ}` with `1/2 + 5iγ/2` a critical zero makes every strict-right zero bad and contradicts no known zero datum. Not provable from zero data; the PW-B coefficient needs a collision-free redesign |
| C14 | **Mellin-continuation rigidity**: self-similarity needs only an analytic continuation of the witness Mellin transform to an open right-closed region containing every pole `1-ρ`; instances: the right half-plane, and the known zero-free region `{Re z > 1/(59 log|Im z|)}` | **building** (unconditional partial producer: seam contraction of the rigidity domain to the known zero-free region) |

### PM-19 (proved, Lean) — Mellin-continuation rigidity; seam contraction to the known zero-free region

Module `RHTower/FermiNymanWitnessContinuationRigidity.lean` (wired into `RHTower.lean`, axioms
`propext, Classical.choice, Quot.sound`, lint clean):
- `IsMellinContinuation w a G Ω`: `G` analytic on an open `Ω ⊇ {Re z > a}`, closed under moving right
  on horizontal lines, `G = W` on `Re z > a`.
- `IsMellinFermiWitness.strip_product`: `(1-2^{-z}) W(z) Ξ(1-z) = -2^{-z} z (1-z) Φ₀(1-z)` on the strip,
  no nonvanishing hypothesis; `IsMellinContinuation.product_identity` extends it to `Ω ∩ {Re z<1}`
  by the identity theorem (`isPreconnected_inter`: horizontal segment to the line `Re z = (a+1)/2`).
- `IsMellinContinuation.selfSimilar`: if `Ω` contains every pole `1-ρ` (`Ξ(ρ)=0`) then `w(t/2)=w(t)`.
  The glued defect `continuedDefect` is entire, equals the exponent-`a` transform `U` wherever
  `ζ(1-z) ≠ 0`, inherits its polynomial growth and integer decay, vanishes, Fourier uniqueness.
  No majorant rate at the exponent (contrast `selfSimilar_of_removable`).
- Instances: `selfSimilar_of_continuation_halfPlane` (`Ω = {Re z > 0}`);
  `selfSimilar_of_continuation_zeroFreeRegion` with the explicit region
  `{Re z > a} ∪ {Re z > 0, |Im z| < 4} ∪ {Re z > 1/(59 log max(|Im z|,2))}` (uses
  `re_le_one_sub_of_riemannZeta_eq_zero`, width `1/(58 log|γ|)` from `|γ| ≥ 4`);
  `selfSimilar_of_sq_continuation_zeroFreeRegion` for continuous square-integrable witnesses.
Meaning: the rigidity domain of the Mellin continuation of an L² witness is no longer the right
half-plane (PM-15) but the known zero-free region; any future zero-free region transports through
`IsMellinContinuation.selfSimilar` verbatim. RH in this language: every L² witness's Mellin transform
continues to the whole strip `0 < Re z ≤ 1/2`; the poles `1-ρ` are the only obstruction, their
residues are the correlation jets `Φ₀(ρ)`. Producer status: the sliver `0 < Re z < 1/(59 log|Im z|)`
is the only part of the strip currently free of hypothesis — Wall 1 unchanged.
- PM-19 addendum: `exists_vk_selfSimilar_of_continuation` — there is a height `γ₁ ≥ e^e` such that
  continuation to `vkContinuationRegion a γ₁ = {Re z > a} ∪ {Re z > 0, |Im z| < γ₁+1} ∪
  {Re z > w(max(|Im z|,γ₁))/2}`, `w(T) = (log T)^{-2/3}(log log T)^{-5/3}/10⁸`, forces self-similarity
  (`abs_re_sub_half_le_vinogradovKorobov`). The hypothesis-free sliver is now of Vinogradov–Korobov
  shape. Module `FermiNymanWitnessContinuationRigidity.lean`, 547 lines, axioms standard, wired.

## 2026-10-17 producer loop, round 3 (Fable) — FZZ-P only

Frame fixed by the corpus (`FermiNyman*`, `BaezDuarteCriterionHardDirection`, `BalazardSaiasYor*`):
`RH ⟺ h ∈ cl span{φ_a} ⟺ W self-similar ⟺ q ≥ 0 on W ⟺ ind₋(q|W) = 0 ⟺ no pole of the left defect at
any mirror zero 1−ρ` (all [L]). The task is the producer. Loop targets below are stated as conjectures
with the mechanism they would need; kills name the wall.

Exact structural facts established on paper this round (used to judge the conjectures):
- Mellin symbols on `Re s > 1/2`: `ĥ(s) = (1−2^{1−s})/s = I(s)·O_h(s)` with `I(s) = (1−2^{1−s})/(√2(1−2^{−s}))`
  unimodular on `Re s = 1/2` (zeros exactly at `1 + 2πik/log 2`, k ∈ ℤ: the dyadic lattice Blaschke product
  `B_sp` times the Blaschke factor at `1`), `O_h(s) = √2(1−2^{−s})/s` outer with bounded inverse. Generator
  symbol `−a^{−s} I(s) O_h(s) ζ(s) = −a^{−s} B_sp(s)·[√2(1−2^{−s}) Ξ(s)/s²]`. Hence
  `M = B_sp·cl span{a^{−s} Ξ(s)/s² : a ≥ 1}` and `RH ⟺ Ξ(s)/s² is outer on Re s > 1/2` (Beurling's form of
  Nyman–Beurling). The dyadic structure is exactly one explicit unimodular decoration: no information.
- Explicit lattice Blaschke product: `B_sp(s) = s(1−2^{1−s})/(√2 (s−1)(1−2^{−s}))`.
- `q(w) = −½ ∫_0^1 h |w|²` (since `D*D = 2·1_{(0,1/2]}`): RH ⟺ `h ⟂ W` ⟺ `h ⟂ W·W̄` ⟺ `h` annihilates the
  algebra generated by `W` (under RH that algebra is the log-2-periodic functions).
- Differentiating `∫_{S_a} w = 0` in `a`: continuous witnesses satisfy the alternating dilation equation
  `Σ_{n≥1} (−1)^{n+1} w(u/n)/n = 0`, i.e. `w(u) = Σ_{n≥2} (−1)^n w(u/n)/n` (conditionally convergent):
  the top octave is a signed average of dilated lower octaves; a witness is determined by its germ at 0.
- `w ⟂ W_sp ⟺ Σ_{j≥0} 2^{−j} w(2^{−j}u) = (∫w / log 2)/u` on `(1/2,1]` (dyadic periodization is a pure
  `1/u` on the top octave). RH ⟺ this linear system together with the witness equation has only the zero
  solution (Fredholm-alternative form; solution space ≅ off-line zero space by PM-18).

| cycle | conjecture | verdict |
|---|---|---|
| C15 | integer dilations give the same closed span: `cl span{φ_n : n ∈ ℕ} = cl span{φ_a : a ≥ 1}` (C13 reopened) | **false**: every `φ_n`, n ≥ 2, vanishes on `(1/2,1]` and `φ_1 = −1` there, so the integer span is constant on `(1/2,1)` while `φ_{3/2}` jumps at `2/3`. Only the target statement survives: `h ∈ cl span{φ_n} ⟺ RH` (Báez-Duarte hard direction is already [L] in `BaezDuarteCriterionHardDirection`). C13 closed. |
| C16 | quantitative unique continuation from `0`: `‖w‖_{L²(δ,1]} ≤ C(δ) ‖w‖_{L²(0,δ]}` on `W` | not provable unconditionally: in model-space coordinates it is invertibility of the compressed shift `P_{K_B} e^{−Tλ}` on `K_B`; by the Sz.-Nagy–Foiaş corona condition this fails if `inf (|e^{−Tλ}| + |B(λ)|) = 0`, which happens when off-line zeros have positive density (|B(Λ+it)| → 0 along vertical lines). Under RH `C(δ) < ∞` (`B_sp` explicit). Qualitative version survives (C17). |
| C17 | qualitative unique continuation: an L² witness vanishing a.e. on `(0,δ]` vanishes; corollaries: self-similarity on `(0,δ]` propagates (apply to `w − w(·/2) ∈ W`); the generators restricted to `(δ,1]` are complete in `L²(δ,1]` for every `δ ∈ (0,1)` | **survives, unconditional** — building (`FermiNymanWitnessGermRigidity`). Mechanism: dilation average → continuous witness vanishing on `(0,δ]` → bounded → self-similar (`selfSimilar_of_bounded`) → zero; back to `w` by interval pairings and Lebesgue differentiation. Meaning: no bulk obstruction; FZZ-P is exactly the control of approximant energy near `t = 0` for every target, not only `h`. |
| C18 | `Ψ_ρ(t) = t^{−ρ}∫_0^t u^{ρ−1} φ_1(u) du` (Mellin symbol `η(z)/(z(z−ρ))`) lies in `M` for every zero `ρ`; RH ⟺ this for all zeros | restatement: `Ψ_ρ = −∫_1^∞ b^{ρ−1} φ_b db` converges in `L²` iff `Re ρ < 1/2` (`‖φ_b‖ = √(log 2/b)`); for `Re ρ > 1/2` the pairing with the zero witness is the residue. The Fubini failure at `Re s = 1/2` is Wall 1. |
| C19 | concentration constant `c* = sup_W ∫_{1/2}^1|w|²/‖w‖²`: prove `c* < 1` unconditionally and push to `1/2` | `c* = 1/2 ⟺ RH`; `c* < 1` is C16 in disguise (restriction to `(0,1/2]` with closed range); no mechanism. |
| C20 | spectral synthesis `W = cl span{g_k} ⊕ cl span{zero witnesses and jets}` (PM-19) without Beurling–Lax | needs `H²`-divisibility by the infinite Blaschke product of the off-line zeros and Beurling's cyclicity of the outer factor; not available in the corpus's Mellin layer (the disk `H²` layer `HardyDiskModelSpace` is coefficient-sequence based). If built, it proves formally that `W = K_{B_η}`: FZZ-P is a restatement of the zero set (census core (c)). Deferred: no producer value. |
| C21 | outerness of `Ξ(s)/s²` via a Herglotz twist `Re(G·Ξ/s²) > 0` with `G` outer | Herglotz ⟺ Weil-positive (corpus bridge); Wall 2 / Wall 8. |
| C22 | Jensen closing: upper bound `P[log|F|](σ₀) ≤ log|F(σ₀)|` from `P[|F|^p](σ₀)` | impossible: `|F|^p` is subharmonic for every `p > 0`, so `P[|F|^p](σ₀) ≥ |F(σ₀)|^p` with equality only for constants. Wall 2 exactly. |
| C23 | the algebra generated by the generators (products `1_{S_a ∩ S_b}`) is dense and stays near `M` | products leave `M`: `φ_1 φ_2 = 1_{⌊1/t⌋ ≡ 3 (4)}` has symbol involving `L(s,χ_4)`; the algebra is the all-characters NB system (W1C territory). |
| C24 | lattice-shift symmetry: multiplication by `g_k` preserves `M` | false: `B_sp(s+2πik/log 2) = B_sp(s)·(s+iκ)(s−1)/(s(s−1+iκ))`; the pole of `ζ` (factor `s/(s−1)`) breaks the dyadic translation symmetry — the pole masks the lattice as it masks the zeros. |
| C25 | log-Möbius head energy `E(X) = ∫_1^X (ψ(x) − 2ψ(x/2))² dx/x²`: `RH ⟺ E(X) = o(log² X)` as a producer | receiver (`E = O(X^ε) ⟹ ZFR(1/2+ε/2)` by Landau; `RH ⟹ E ≪ log X` is Cramér's mean square); and the family needs simple zeros (`PMLogMobiusBoundaryMultiplicity`). |
| C26 | asymptotic self-similarity: `‖w(·/2) − w‖_{L²(0,δ]} = o(‖w‖_{L²(0,δ]})` as `δ → 0` forces `w(·/2) = w` | the ratio is a constant `|2^{1−ρ̄} − 1|` on zero witnesses, `0` on spurious ones; the statement is RH restated at the germ; no mechanism beyond C17 |
| C27 | sieve/sawtooth form: `RH ⟺ ∃ weights (c_d)_{d≤N}` with `x ↦ Σ_d c_d{x/d}` close to `−1_{[1,∞)}` in `L²(dx/x²)`, i.e. the sieve function `Σ_{d∣m} c_d` has summatory function tracking the line `1 + x Σ c_d/d` in mean square | exact Möbius (`c = −μ`) pays `N H_N²` (harmonic floor); Barban–Vehov pays `N (L_N − 1)²/log² N + M(N)²/N`, which under RH is `N^{2ε}/log² N` and tends to `0` only if `M(N) ≪ N^{1/2} (log N)^{1−ε}`: the natural families need Mertens-size information beyond RH (consistent with `PMLogMobiusBoundaryMultiplicity`). Wall 1. |
| C28 | BSY vs Haar distance: `dist(h,M)² ≤ C Σ_ρ log²|γ_ρ| · log|ρ/(1−ρ)|` (zero-free-region bound `|B_sp(ρ)| ≫ 1/log|γ|`) | receiver inequality between two off-line functionals; both vanish iff RH; no producer value. Not built. |

### PM-20 (proved, Lean) — germ rigidity and unconditional local completeness

Module `RHTower/FermiNymanWitnessGermRigidity.lean` (492 lines, wired into `RHTower.lean`, axioms
`propext, Classical.choice, Quot.sound`, lint clean):
- `IsFermiNymanWitness.eq_zero_of_eqOn_zero`: a continuous witness vanishing on `(0,δ]` vanishes on
  `(0,1]` (bounded ⟹ exponent `0` ⟹ self-similar ⟹ `w(t) = w(t/2^k) = 0`).
- `IsFermiNymanWitness.selfSimilar_of_selfSimilar_near_zero`: self-similarity on `(0,δ]` propagates
  to `(0,1]` (`w − w(·/2)` is a witness).
- `IsL2FermiWitness.ae_eq_zero_of_ae_eq_zero_near_zero`: a measurable `L²` witness vanishing a.e. on
  `(0,δ]` vanishes a.e. (dilation averages `η⁻¹ t ∫_{t/(1+η)}^t w u⁻²` are continuous witnesses
  vanishing on `(0,δ]`, hence zero ⟹ `∫_s^t w u⁻² = 0` for all `0<s<t≤1` ⟹ Lebesgue differentiation).
- `fermiGenSpanOn_topologicalClosure_eq_top`: for every `δ > 0` the restricted generators span a dense
  subspace of `L²(δ,1]`; `exists_fermiNymanCombination_approx_on`: every `f ∈ L²(δ,1]` is an `L²(δ,1]`
  limit of finite generator combinations; Haar instance `exists_fermiNymanCombination_dyadicHaar_approx_on`.
- `norm_dyadicInnerFactor_eq_one`, `integral_dyadicHaar_mul_cpow_factor`, `mellin_fermiNymanGen_factor`:
  `ĥ(s) = I(s)·√2(1−2^{−s})/s`, `M[φ_a](s) = −a^{−s} I(s)·√2(1−2^{−s})ζ(s)/s`, `|I| = 1` on `Re s = 1/2`.
Meaning (frontier): the alternating system has **no bulk obstruction** — on every `(δ,1]` it is
complete for every target, unconditionally; a witness is determined by its germ at `0`; the whole RH
content of FZZ-P is the energy of approximants on `(0,δ)` as `δ → 0`, equivalently the growth of
witnesses at the origin (poles of the Mellin continuation at the mirror zeros). The dyadic decoration is
one explicit unimodular factor on both sides, so FZZ-P is exactly Beurling's outer-function form of
Nyman–Beurling for `Ξ(s)/s²` (`(s−1)ζ(s)/s²` outer on `Re s > 1/2`). Producer status: Wall 1 unchanged.

### PM-21 (proved, Lean) — germ laws: linear mass at the origin, log-mean on the top octave

Target set by the user after PM-20: "control global L² approximation at 0, equivalently all global
witnesses' dyadic self-similarity". The germ of a witness is measured by its mass function
`m_w(x) = ∫_0^x |w|²`. Module `RHTower/FermiNymanWitnessGermLaws.lean` (wired, axioms standard, lint clean):
- `IsL2FermiWitness.ae_selfSimilar_iff_linearMass` (**unconditional dichotomy**): an L² witness is a.e.
  dyadically self-similar ⟺ `m_w(x) ≤ C x` on `(0,1]`. Mechanism ⟸: under linear mass every dilation
  average is bounded by `η⁻¹(1+η)²√C` (`norm_dilationAverage_le_of_linearMass`), hence a bounded continuous
  witness, hence self-similar; `w_η(t/2) = w_η(t)` with the primitive form and `u ↦ u/2` gives
  `∫_s^t (w(u/2) − w(u)) u⁻² = 0` for all `0<s<t≤1` (`setIntegral_sub_comp_half_div_sq_eq_zero`), then
  Lebesgue differentiation (`ae_eq_zero_Ioc_of_forall_setIntegral_Ioc_eq_zero`). ⟹: `m(x/2) = m(x)/2`.
- `riemannHypothesis_iff_forall_l2FermiWitness_linearMass`: **RH ⟺ every L² witness has at most linear
  mass at the origin**; `riemannHypothesis_iff_forall_l2FermiWitness_dyadicMass_bounded`: RH ⟺ the dyadic
  dilation is power-bounded on witnesses (`2^k m_w(2^{−k}) ≤ C`). Zero witness: `m = x^{2σ−1}/(2σ−1)`,
  superlinear (`not_linearMass_powerWitness`). Also `IsL2FermiWitness.ae_selfSimilar_of_riemannHypothesis`.
- `riemannHypothesis_iff_fermiNymanWitness_dyadicLogMean_eq_zero`: **RH ⟺ `∫_{1/2}^1 w(t)dt/t = 0` for every
  continuous witness** — a single linear functional (the pairing with `t⁻¹1_{(1/2,1]}`, Mellin symbol
  `B_sp(s)·√2(1−2^{−s})/s`), versus the quadratic half-mass criterion. Zero witness value
  `(1−2^{1−ρ̄})/(ρ̄−1) ≠ 0` (`dyadicLogMean_powerWitness`).
Meaning: the germ-control target is now stated exactly: RH ⟺ no witness carries superlinear mass at
`0` ⟺ `sup_k ‖D^k|_W‖ < ∞` (spectral radius of the dyadic dilation on `W` is `2^{1−inf Re ρ}` over
off-line zeros). Structural kill recorded: every inequality derivable from the witness equation alone is
satisfied by the zero witnesses `t^{ρ̄−1}` (they solve it), so no estimate internal to `W` can force
linear mass; the only input is the zero set of `η` (restatement core (c)). Producer status: Wall 1.
