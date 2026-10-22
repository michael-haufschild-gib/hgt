# The Weil lag function: Bochner form of the fixed-pole criterion, and prime rigidity

- **ID:** `weil-lag-function-bochner-form`
- **Stage:** 1-in-progress (paper proofs complete for every statement below; Lean: §1–§4 certified, including
  `RH ⟺ Φ bounded`, see `3-formalized/lag-explicit-formula-lean.md`; open on paper: §6 Krein determinacy)
- **Parents:** `fixed-pole-zero-margin-law.md`, `3-formalized/archimedean-genus-zero-sum-lean.md`
- **STATUS entries:** CANNOT-325 (corrected), MUST-232, MUST-233, MUST-234
- **Computations:** `2-fully-proven/computations/lag-function-pd-horizon/`, `lag-function-pd-rigidity/`

## 1. Definition and unconditional properties

`Φ(L) := Σ_ρ e^{L(ρ−1/2)}/(ρ(1−ρ))`, sum over the nontrivial zeros with multiplicity.

- Absolutely convergent for every real `L`: `|e^{L(ρ−1/2)}| = e^{L(β−1/2)} ≤ e^{|L|/2}` and `Σ_ρ 1/|ρ(1−ρ)| < ∞`
  (corpus `xiSpectralPoint_inv_sq_summable`). Continuous by dominated convergence. Even (`ρ ↦ 1−ρ`). Real (`ρ ↦ ρ̄`).
- `Φ(0) = Σ_ρ 1/(ρ(1−ρ)) = 2 + γ − log 4π` — Lean, `RHTower.ArchimedeanGenusZeroSum`.

## 2. The pole family Gram formula (paper theorem)

For `f_a = e^{x/2}1_{[−a,a]}`, `f̂_a(s) = ∫_{−a}^a e^{sx}dx = 2sinh(as)/s`, and the Weil pairing
`Q(f,g) = Σ_ρ f̂(ρ)·conj(ĝ(1−ρ̄))` gives `Q(f_a,f_b) = Σ_ρ 4sinh(aρ)sinh(b(1−ρ))/(ρ(1−ρ))`. With
`4sinh u sinh v = 2cosh(u+v) − 2cosh(u−v)`, `u+v = b + (a−b)ρ`, `u−v = (a+b)ρ − b`, and `Φ(−L) = Φ(L)`:

> `Q(f_a, f_b) = 2cosh((a+b)/2)·Φ(a−b) − 2cosh((a−b)/2)·Φ(a+b)`.

Diagonal: `Q(f_a) = 2cosh(a)Φ(0) − 2Φ(2a)`, which reproduces the corpus's `A(a)` (the `O(e^{−a})` remainder is
`e^{−a}(Φ(0) + 2B(e^{2a}))`). The reflected pair `p_± = e^{±x/2}1_{[−a,a]}` gives the twisted sum
`Q(p_+,p_−) = Σ_ρ 4sinh²(aρ)/ρ²`, the corpus's `C(a)`; `Φ` is the untwisted object.

## 3. Prime side (paper theorem; classical explicit formulas)

For `X > 1` (non-prime-power; at prime powers take the mean value, `Φ` is continuous):
`ψ(X) = X − Σ_ρ X^ρ/ρ − log 2π − ½log(1−X^{−2})` and, from `(1/2πi)∫(−ζ'/ζ)(s)X^s/(s−1)ds = Σ_{n≤X}Λ(n)X/n`,
`Σ_ρ X^ρ/(ρ−1) = X(log X − γ − Σ_{n≤X}Λ(n)/n) + X·artanh(1/X) − 1`. Since `1/(ρ(1−ρ)) = 1/ρ + 1/(1−ρ)`,

> `Φ(L) = e^{−L/2}(X − ψ(X)) + e^{L/2}(Σ_{n≤X}Λ(n)/n − L + γ) − e^{−L/2}B(X)`, `X = e^L`,
> `B(X) = log 2π − 1 + ½log(1 − X^{−2}) + X·artanh(1/X)`,

equivalently `Φ = Φ_arch + Σ_{n≤X} 2Λ(n)n^{−1/2}sinh((L − log n)/2)`, `Φ_arch(L) = e^{L/2}(1+γ−L) − e^{−L/2}B(e^L)`.
The two logarithmic singularities of `B` at `X = 1` cancel (`(½ − X/2)log(X−1) → 0`), `B(1+) = log 4π − 1`, and
`Φ_arch(0+) = 2 + γ − log 4π = Φ(0)`: consistency of the prime side with the Lean-certified zero side. Numerically the
prime side agrees with the zero side (1500 zeros) to `10⁻⁶` on `0.3 ≤ L ≤ 12`.

## 4. The criterion (paper theorem)

RH ⟺ `Φ` bounded ⟺ `|Φ(L)| ≤ Φ(0)` for all `L` ⟺ `Φ` positive-definite.
- RH ⟹ `Φ(L) = Σ_ρ e^{iγL}/|ρ|²`: transform of the positive finite measure `Σ_ρ δ_γ/|ρ|²`, so `|Φ| ≤ Φ(0)` and PD.
- `Φ` bounded ⟹ RH: `F(s) = ∫_0^∞ Φ(L)e^{−sL}dL` is analytic on `Re s > 0`; for `Re s > 1/2` Fubini gives
  `F(s) = Σ_ρ 1/((s − (ρ − ½))ρ(1−ρ))`, a Mittag-Leffler series converging locally uniformly off its poles, hence
  meromorphic on `ℂ` with a pole of residue `m_ρ/(ρ(1−ρ)) ≠ 0` at each `ρ − ½`; a zero with `β > ½` would put a pole in
  `Re s > 0`. Zeros with `β < ½` are excluded by `ρ ↦ 1−ρ`.
- Under RH and simple zeros, `Φ` is the Besicovitch mean autocorrelation of Cramér's function
  `Ψ(x) = Σ_ρ e^{x(ρ−½)}/ρ = e^{−x/2}(e^x − ψ(e^x)) + O(e^{−x/2})` (`x>0`), so the criterion is Cramér's mean-square
  criterion `∫_1^X (ψ(t)−t)²t^{−2}dt = O(log X)`.

**Reading of the "sharp constant".** The one-sided constant `Σ_ρ|ρ|^{−2}` of the fixed-pole criterion is `Φ(0)`, the
value of the same function at zero lag; `|Φ(L)| ≤ Φ(0)` is the trivial inequality for a positive-definite function.
Nothing is to be *estimated*; the content is positive-definiteness.

## 5. Positive-definiteness pins the primes (theorems under RH; numerics unconditional)

- **Horizon.** With prime powers `≤ P` kept, `Φ_P` fails the Toeplitz test on `[−L,L]` at `L = log n₁ + δ`,
  `δ ∈ [0.013, 0.05]` for all 42 tested `P ≤ 2048` (`n₁` the next prime power); the two-by-two test fails within
  `2arcsinh(Φ(0)√n₁/Λ(n₁))` under RH because `Φ ≤ Φ(0)` and the omitted kink grows.
- **Local rigidity.** Perturbing one kink's position or weight by `ε ≠ 0` destroys positive-definiteness on any window
  containing it: the perturbation's transform is a signed density `~ εΛ(n)n^{−1/2}sin(ξ log n)/ξ`, exceeding the
  atomic zero measure's density `log ξ/(2πξ²)` at high frequency and negative on half of every period, while the
  window's Toeplitz operator `Σ_ρ|ρ|^{−2}|e_γ⟩⟨e_γ|` has no spectral gap. Measured tolerance `10⁻⁵…10⁻⁴` on a
  500-point grid, a grid-limited shadow of the exact statement.

## 6. Verdict and what remains

Sections 1–4 are `REDISCOVERED` in substance (Bochner form of Weil positivity; Cramér 1921; the explicit formulas),
new only as the exact Gram formula of §2 and the identification of the sharp constant with `Φ(0)` (Lean). Section 5 is
new: a quantitative and an exact rigidity law for the prime side under positivity, with the producer consequences of
MUST-234 (marginal positivity, no spectral gap; no approximate prime input). `[OPEN CORE]` unchanged: positivity itself.
Krein determinacy of the archimedean germ (uniqueness of the PD extension of `Φ_arch|[−log 2, log 2]`) is open and
expected false; a proof either way would decide whether the archimedean place plus positivity determines the primes.

**Lean.** The prime side of §3 is now a theorem (`LagExplicitFormula.lag_explicit_formula`), proved by termwise
residue calculus on the Mittag-Leffler expansion with the kernel `1/(s(s−1))` (no truncated Perron, no zero-density
input); `Φ`, its evenness, `Φ(0)`, the prime side and `RH ⇒ |Φ| ≤ Φ(0)` are in `WeilLagFunction`. The converse `Φ bounded ⇒ RH` is
`WeilLagFunctionCriterion.riemannHypothesis_of_weilLagFunction_bounded`; the criterion
`riemannHypothesis_iff_weilLagFunction_bounded` is closed.

## 7. The integer lag law (paper proof; Lean-closed in `WeilLagFunctionInteger`, `WeilLagFunctionRecurrence`)

**Definition.** `a_n := Φ(log n)`. By §3 at `X = n ≥ 2`:
`a_n = [(n − ψ(n)) + n(M(n) − log n + γ) − log 2π + S(n)]/√n`, `M(n) = Σ_{m≤n}Λ(m)/m`, `S(n) = Σ_{k≥1} n^{−2k}/(2k(2k+1))`;
`a_1 = Φ(0) = 2 + γ − log 4π` (§1), since `S(1) = 1 − log 2`.

**Lemma 7.1 (interval bound).** For `L ≥ log 2`, `n = ⌊e^L⌋`: `|Φ(L) − a_n| ≤ 30`.
*Proof.* Write `X = e^L`, `s_X = √X`, `s_n = √n`, and note `ψ(X) = ψ(n)`, `⌊X⌋ = n`. Then
`Φ(L) − a_n = (s_X − s_n) + ψ(n)(1/s_n − 1/s_X) + (s_X − s_n)(M(n) − L + γ) + s_n(log n − L) + log 2π (1/s_n − 1/s_X) + (S(X)/s_X − S(n)/s_n)`.
Pieces: `0 ≤ s_X − s_n ≤ 1/(2s_n) ≤ 1`; `0 ≤ ψ(n)(1/s_n − 1/s_X) ≤ 2n log n · 1/(2n s_n) = log n/s_n ≤ 2` (using `ψ(n) ≤ (n+1)log n`,
`1/s_n − 1/s_{n+1} ≤ 1/(2 n s_n)`, `log n ≤ 2√n`); `|M(n) − L + γ| ≤ (log n + 2)²` (`M(n) ≤ log n · H_n ≤ log n(1 + log n)`,
`log n ≤ L ≤ log n + 1/n`, `γ ≤ 1`) and `(log n + 2)² ≤ 36√n` (`log n ≤ 4n^{1/4}`), so `|(s_X − s_n)(M(n) − L + γ)| ≤ 18`;
`−1 ≤ s_n(log n − L) ≤ 0`; `0 ≤ log 2π(1/s_n − 1/s_X) ≤ 6`; `−1 ≤ S(X)/s_X − S(n)/s_n ≤ 0` (`S` decreasing, `0 ≤ S ≤ S(1) < 1`).
Sum: `−20 ≤ Φ(L) − a_n ≤ 27`. ∎

**Theorem 7.2 (integer criterion).** `RH ⟺ (a_n)_{n≥2}` bounded above `⟺ (a_n)_{n≥2}` bounded below `⟺ ∀ n ≥ 1, a_n ≤ a_1`.
*Proof.* RH ⇒ `|a_n| ≤ a_1` by §4. Conversely, if `a_n ≤ M` for `n ≥ 2`: for `L ≥ log 2`, `Φ(L) ≤ M + 30` (7.1); for `|L| ≤ log 2`,
`|Φ(L)| ≤ e^{|L|/2} Σ_ρ|ρ(1−ρ)|^{−1} ≤ √2 W`; `Φ` is even; so `Φ` is bounded above and §4 (one-sided, MUST-237) gives RH.
Bounded below: same with the lower half of 7.1. ∎

**Theorem 7.3 (dichotomy).** Either `|a_n| ≤ a_1` for all `n`, or `(a_n)` is unbounded above and unbounded below. (7.2 both ways.)

**Theorem 7.4 (recurrence to the ceiling).** Assume RH. For every base `b` and `ε > 0` there is `m ≥ 1` with `a_1 − ε < a_{b^m} ≤ a_1`;
hence `sup_{n≥2} a_n = a_1`.
*Proof.* Under RH `ρ = ½ + iγ`, `ρ(1−ρ) = ¼ + γ²`, so `Φ(L) = Σ_ρ w_ρ cos(γL)` with `w_ρ = (¼+γ²)^{−1} > 0`, `Σ w_ρ = a_1`
(absolutely convergent; the imaginary parts cancel because `Φ` is real). Pick a finite set `F` of zeros with `Σ_{ρ∉F} w_ρ < ε/4`,
put `Q = ⌈8π²a_1/ε⌉ + 1`, and apply simultaneous Dirichlet approximation to the `|F|` numbers `γ log b/2π`: some `m ∈ [1, Q^{|F|}]`
has `‖mγ log b/2π‖ < 1/Q` for all `ρ ∈ F`, hence `cos(γ m log b) ≥ 1 − (2π/Q)²/2 =: 1 − δ` with `δ a_1 ≤ ε/4`. Then
`a_{b^m} = Φ(m log b) ≥ (Σ_F w_ρ)(1 − δ) − Σ_{ρ∉F} w_ρ ≥ (a_1 − ε/4) − ε/4 − ε/4 > a_1 − ε`. ∎

**Remarks.** (i) The ceiling is attained by no `n ≥ 2` under RH (all `cos(γ log n) = 1` would make the ordinates commensurable,
contradicting `N(T) ∼ (T/2π)log T`), but it is the exact supremum along every geometric progression. (ii) The floor is
asymmetric: `inf a_n = −a_1` needs all `cos(γ log n) ≈ −1` simultaneously, a ℚ-independence property of the ordinates that
Dirichlet approximation cannot give; only `inf a_n < 0` is forced (`Φ` has Bohr mean `0` under RH). (iii) For a producer this is
the zero-margin law at integer lags: a proof of `a_n ≤ a_1` cannot lose any constant along `b^m`, and it must know the joint
distribution of the phases `γ log b` exactly — the same obstruction as `fixed-pole-zero-margin-law`, now with the sharp
recurrence set identified.

## 8. The unconditional `Ω±(√n)` law (paper proof; Lean-closed in `WeilLagFunctionOmega`)

**Theorem 8.1.** Unconditionally: for every `ε > 0`, `a_n > a_1 − ε` for infinitely many `n`; and there is `η > 0` with
`a_n ≤ −η` for infinitely many `n`. In prime language `E(n) = Ω₊((a_1 − ε)√n)` and `E(n) = Ω₋(η√n)`.
*Proof.* If RH fails, `(a_n)` is unbounded above and below (7.3). Assume RH. The positive side is 7.4. For the negative
side: `Φ(L) = Σ_ρ w_ρ e^{iγ L}` is an absolutely convergent exponential series, hence Bohr almost periodic, with Bohr mean
`Σ_{γ = 0} w_ρ = 0` (no zero has ordinate `0`, since `ξ(½) ≠ 0`). Suppose for every `η > 0` that `Φ(L) > −η` for all large `L`.
Then `Φ⁻ = max(−Φ, 0)` is almost periodic (a `1`-Lipschitz image) and tends to `0`, so by the vanishing lemma `Φ⁻ ≡ 0`,
i.e. `Φ ≥ 0` everywhere. A nonnegative almost-periodic function with mean `0` vanishes identically, contradicting
`Φ(0) = a_1 > 0`. Hence some `η > 0` has `Φ(L) ≤ −η` at arbitrarily large `L`. The transfer to integers: the interval bound
of 7.1 sharpens to `|Φ(L) − a_{⌊e^L⌋}| ≤ 3(log n + 2)²/√n` (the same six pieces, kept in units of `1/√n`), which tends to
`0`; so `a_n ≤ −η/2` for arbitrarily large `n`. ∎

**Theorem 8.2.** `RH ⟺ Φ` is Bohr almost periodic (`Φ` is continuous unconditionally; almost periodic ⇒ bounded ⇒ RH; RH ⇒
exponential series ⇒ almost periodic).

**Reading.** The sign of `E(n)` carries no information about the zeros: both signs occur infinitely often in every case. RH
lives entirely in the *size* of the positive excursions, whose exact ceiling is `a_1√n`; the negative excursions have the
ceiling `−a_1√n` under RH but its attainment is a ℚ-independence statement about the ordinates.

## 9. The floor law (paper proof; Lean-closed in `WeilLagFunctionFloor`)

**Definition.** The ordinates have *no odd relation* if for every finite set `Γ` of distinct ordinates and every
`c : Γ → ℤ` with `Σ c_γ γ = 0` the sum `Σ c_γ` is even.

**Theorem 9.1.** Assume RH. Then `inf_{n≥2} a_n = −a_1` iff the ordinates have no odd relation.

*Proof (⟹).* Let `Σ_{γ∈Γ} c_γ γ = 0` with `Σ c_γ` odd. For `ε > 0` pick `L` with `Φ(L) < −a_1 + ε`. Since
`Φ(L) + a_1 = Σ_ρ w_ρ(1 + cos γL)` with positive terms, each `γ ∈ Γ` has `1 + cos(γL) < ε(¼ + γ²)`, i.e.
`‖e^{iγL} + 1‖ < √(2ε(¼+γ²))`. With `u_γ = −e^{iγL}` (unimodular, `‖u_γ − 1‖` small) the relation gives
`1 = e^{iL Σ c_γ γ} = Π (−u_γ)^{c_γ} = (−1)^{Σ c_γ} Π u_γ^{c_γ} = −Π u_γ^{c_γ}`, so `‖Π u_γ^{c_γ} − 1‖ = 2`, while
`‖Π u_γ^{c_γ} − 1‖ ≤ Σ |c_γ| ‖u_γ − 1‖ ≤ √(2ε) Σ|c_γ|√(¼+γ²) → 0`. Contradiction for small `ε`.

*Proof (⟸).* Fix `ε`. Take a finite set `F` of zeros with tail weight `< ε/8`, `Γ` its ordinates, and a rationally
independent integral basis `b_1,…,b_k` of the group generated by `Γ` with `b_i = Σ_γ m_{iγ} γ`, `γ = Σ_i n_{γi} b_i`.
Put `θ_i = π Σ_γ m_{iγ}`. For `γ ∈ Γ`, `Σ_i n_{γi} θ_i = π N_γ` with `N_γ = Σ_i n_{γi} Σ_{γ'} m_{iγ'}`, and
`γ − Σ_{γ'} (Σ_i n_{γi} m_{iγ'}) γ' = 0` is a relation with coefficient sum `1 − N_γ`, even by hypothesis; so `N_γ` is
odd and `Π_i e^{i n_{γi} θ_i} = −1`. Kronecker's theorem gives `t` with `e^{i b_i t}` within `δ` of `e^{iθ_i}` for all `i`,
hence `‖e^{iγt} + 1‖ ≤ (Σ_i |n_{γi}|) δ ≤ Kδ` and `cos(γt) ≤ −1 + Kδ` on `Γ`. Choosing `Kδ a_1 ≤ ε/8` gives
`Φ(t) ≤ −a_1 + 3ε/8`. An `ε/8`-almost period `τ` (Bohr) moves `t` to `t' = t + τ` beyond `log(N₁+2)`; then
`n = ⌊e^{t'}⌋ ≥ N₁ + 2` and the sharp gap `3(log n+2)²/√n < ε/8` give `a_n < −a_1 + ε`. ∎

**Reading.** Ceiling and floor of the same explicit sequence are governed by different mathematics: the ceiling `a_1` is the
supremum unconditionally on the zeros (7.4), the floor `−a_1` is the infimum exactly under a parity condition on the
integer relations among the ordinates — implied by, and weaker than, the linear independence conjecture.

## 10. Conjecture DGC (discrete geometric criterion) — SURVIVES PRELIMINARY ATTACK

**Conjecture.** For a fixed base `b ≥ 2`: `RH ⟺ (a_{b^m})_{m ≥ 1}` is bounded above (equivalently bounded).

**Status.** `⟹` is Lean (7.2). For `⟸`, the generating function `Σ_m a_{b^m} z^m = Σ_ρ w_ρ/(1 − b^{ρ−½}z)` has poles at
`z_ρ = b^{½−ρ}`, `|z_ρ| = b^{½−β}`. Bounded coefficients force analyticity of the power series in `|z| < 1`, so an off-line
zero (`|z_ρ| < 1`) contradicts boundedness **unless** the Mittag-Leffler function is not genuinely singular at `z_ρ`, which
requires `z_ρ` to be an accumulation point of other poles. Likewise the Landau/Laplace route (measure `Σ_m (M − a_{b^m})δ_{m log b}`)
gives a real singular point at the abscissa `Θ − ½`, which is a pole or an accumulation point of poles `ρ − ½ + 2πik/log b`;
this is excluded only if there is no sequence of zeros with `β_j → Θ = sup β` and `b^{iγ_j} → 1`.

`[OPEN CORE]` **b-resonance:** rule out off-line zeros whose real parts increase to the supremal abscissa while
`b^{iγ_j} → 1`. Nothing known about off-line zeros excludes it; quantifying over all bases does not help (`n^{iγ_j} → 1` for
all `n` is consistent with Bohr recurrence of `ζ` in `σ > 1` and says nothing in the strip). The continuous criterion (7.2)
avoids the issue because poles `ρ − ½` cannot accumulate at a real point (`ξ` has no real zeros).

**What its truth would show.** RH would be a statement about one geometric progression of the explicit sequence; its
falsity would exhibit a resonance between the base and the off-line zeros, a new invariant of a hypothetical counterexample.

## §11 Single-base detection (Lean, `WeilLagFunctionSingleBase`; STATUS MUST-248)

The `b`-resonance open core of §10 is now localised: if the maximal real part `β₀ > ½` is attained, `a_{b^m}` is
unbounded for every base (top level has positive real weight `Re w_ρ > 0`; Dirichlet on the top ordinates; lower
levels are `o(b^{m(β₀−½)})` by dominated convergence — no gap needed). Bounded `a_{b^m}` ⟹ RH ∨ (sup of real parts not
attained) ⟹ RH ∨ infinitely many off-line zeros. Remaining open core for one-prime-orbit sufficiency: real parts
accumulating at `Θ` from below with no zero at `Θ`, the near-aliasing regime `ρ_q ≈ ρ₁ + 2πik/log b`, `β_q → β₁`.

## §12 Shadow law (Lean, `WeilLagFunctionShadow`; STATUS MUST-249)

Generating-function form of the single-base question: `P(t) = Σ_m a_{b^m} t^m` analytic on `|t| < 1` if bounded;
`P = Σ_q w_q/(1 − z_q t)` near `0`; every `1/z_q` is a genuine pole (aliased residues add with positive real part).
Identity theorem along the segment `[0, 1/z_{q₀}]` (convex tube, `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`)
⟹ the other poles accumulate on the segment. Remaining open core (one-prime-orbit sufficiency): the sealed case —
the derived set of `{1/z_q}` contains a closed curve around `0` inside the unit disc, i.e. a belt of accumulation of
zeros mod `2πi/log b` above every isolated off-line zero. Abstract question: can a positive discrete measure on an
annulus with non-attained outer radius `R > 1` have bounded moments? Continuous rotation-invariant measures do
(all moments vanish); on a single circle Wiener's lemma forbids it; with radii accumulating at `R` it is open here.

## §13 The sealed belt exists (Lean, `RingRecursionWitness`; STATUS CANNOT-327)

Verdict on the sealed-belt conjecture of §12: **FALSE as a structural statement**. Explicit witness: rings of `N`-th
roots of unity at radius `e^{−5/√N}`, rotation flag and weight chosen by recursion over proper divisors so that all
power sums at `m` cancel to `±e^{−λm}` (any rate `λ > 0`). Positive summable weights, moduli `→ 1` not attained;
scaling by `R = e^{λ}` gives top modulus `R` not attained and all power sums of modulus `≤ 1`. Note: sub-exponential
decay would not suffice (scaling multiplies the `m`-th sum by `R^m`); the geometric seed is essential.
Hence one-prime-orbit sufficiency needs arithmetic input about the zeros; the lag front of Route O is closed on the
structural side: MUST-248 (attained top), MUST-249 (shadow law), CANNOT-327 (no structural proof beyond them).

## §14 Distributional constraints do not rescue the single-base criterion (analysis, 2026-09-06)

Question: does the weight–height tie `w = 1/(ρ(1−ρ))` plus unconditional zero-distribution facts exclude the ring
witness of §13? Answer (paper level): no. Ring `N` can be realised by `N` zeros at real part `β_N = Θ − 5/(√N log b)`
with ordinates `(π(s+2j)/N + 2πK_j)/log b`, `K_j ≈ N³` spread over a window of relative width `N^{−2}` so that the
weights are nearly equal (relative deviation `N^{−2}`); the recursion only needs ring totals within a window of huge
slack (`M/(Rρ_m)^m = M e^{5√m}`) and the sign, which conjugate symmetry keeps real; deviations of ring `N` at non-multiple
exponents feed later rings with ratio `(ρ_N/ρ_m)^m ≈ e^{−2.5(m−N)/√m}`, total `≲ √m · max δ_N ≲ m^{−3/2}`, summable.
Local count (`N` zeros in a height window `≳ 2πN/(3 log N)` at height `N³` — allowed by MUST-246 and Riemann–von
Mangoldt), Bohr–Landau `N(σ,T) = O(T)` (rings give `T^{2/3}`), and Ingham-type bounds (raise the height exponent)
are all satisfied. Landau's formula `Σ_{γ≤T} b^{iγ} = −(T/2π)Λ(b) + O(log T)` is insensitive to the sparse rings.
Two independent bases: the same construction with `K_j` also chosen (Dirichlet, window `N^{a−2} ≥ N³`, `a ≥ 5`) to make
the base-2 angles approximate roots of unity appears to work too, so no finite set of bases decides RH structurally.
Lacunary lags `b^{2^k}` with one-sided (upper) boundedness are blind even to a single off-line pair (`γ log b ≡ 2π/3`).
Conclusion: the only inputs that can close one-prime-orbit sufficiency are the Euler product / functional equation
identities (the prime side of Φ), not zero statistics. Not formalised; recorded as the lane's terminal analysis.
