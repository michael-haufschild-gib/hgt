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
