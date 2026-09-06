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
