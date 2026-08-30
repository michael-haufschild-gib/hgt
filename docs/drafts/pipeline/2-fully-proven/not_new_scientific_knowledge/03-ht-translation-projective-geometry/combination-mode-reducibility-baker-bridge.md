# Combination-mode cocycle reducibility — Baker is load-bearing (Lemma R); the infinite base is the obstruction; reducibility is RH-blind

- **ID:** combination-mode-reducibility-baker-bridge
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), Door grade **BRIDGE**. The proven residue of the (refuted) C5★-as-reducibility lead.
- **Priority:** FOUNDATIONAL
- **Owner:** Wheeler
- **Source / split:** extracted from `../5-failed/combination-mode-baker-reducibility.md` (the C5★-as-reducibility
  conjecture, **REFUTED — RH-blind**). The `σ>¾` threshold worked to conclusion and the relocated RH target live
  in `../1-in-progress/finite-free-convolution-flow.md`.

---

## Terminal context
The C5★ conjecture *"combination-mode reducibility is native/C5 and reducibility ⟺ RH"* was **REFUTED** (it is
RH-blind; `5-failed`). This card banks the genuinely-proven **BRIDGE** residue.

## §1 Lemma R — Baker is load-bearing for combination-mode reducibility `[PROVEN]`
Over the `𝕋^∞` prime-frequency Kronecker flow, a combination-mode cohomological equation `Dh = g` (Fourier
modes `m` of mixed sign, `ĥ(m) = ĝ(m)/(i\,m·ℓ)`, `ℓ = (\log p)_p`):
> **Lemma R.** (i) `m·ℓ ≠ 0` for all `m≠0` (unique factorization) — `ĥ(m)` is *defined*; (ii) for the prime
> frequency, **Baker–Wüstholz** gives `|m·ℓ| ≥ γ·H(m)^{-κ}` (`H(m)=\max(3,\max_p|m_p|)`, effective `γ,κ`), so for
> the analytic `g`, `‖h‖²_{L²} = Σ_j e^{-2ρ|m^{(j)}|}/(m^{(j)}·ℓ)² ≤ γ^{-2}Σ_j e^{-2ρ|m^{(j)}|}H(m^{(j)})^{2κ} < ∞`
> — `h` exists, the cocycle is **reducible**. **Conversely**, for a Liouville-independent frequency `ω′` (same
> modes) one can force `|m^{(j)}·ω′| ≤ e^{-|m^{(j)}|²}` along a subsequence, whence
> `e^{-2ρ|m^{(j)}|}e^{2|m^{(j)}|²}→∞`, `h∉L²` — **not reducible**.

So the same combination-mode equation is **solvable for the prime frequencies and unsolvable for Liouville
frequencies**; the difference is exactly Baker's effective bound. **Both** inputs are load-bearing: unique
factorization to *divide* (`m·ℓ≠0`), Baker to keep the quotient *summable* (`|m·ℓ|` not super-exp small). This
is the **first object in the programme where Baker is genuinely load-bearing** — unlike §59/§60 and the 19a
cocycle, where the qualitative `Λ={0}` sufficed and no effective bound was ever needed. *Door-2:* finite base =
`𝕋^d` KAM/small-divisor (parent) + Baker (parent) → BRIDGE (a deeper bridge than the axis-mode ones).

## §2 The infinite base is the obstruction — uniform Baker FAILS for unbounded support `[PROVEN, negative]`
> **Part 1.** `(\log p)_∞` is **not polynomially Diophantine** over unbounded-support modes. *Dirichlet
> pigeonhole:* among the `N^s` vectors `|m_p|≤N` on a support `S` (`|S|=s`), the values `m·ℓ` lie in an interval
> of length `≤2N Σ_{p∈S}\log p`, so two coincide within `N^{-s}`; their difference has `|m·ℓ| ≤ C·N^{-s} =
> C·e^{-(|m|/2N)\log N}` — **exponentially small in `|m|`**. And Baker–Wüstholz only degrades: its constant
> `C(s)` grows **super-exponentially** in the number of logs `s` (`s!`, `s^s`).

Standard KAM needs a **fixed-exponent** Diophantine condition; the above shows it **fails** for `(\log p)_∞`
over unbounded support. So the naive infinite-support reducibility is **unprovable by KAM and effectively
false** — a native-zone finding: **the infinite base is the obstruction**, not removable by any finite-`d`
parent, and **bounded degree is forced**.

## §3 The bounded-degree carrier has combination-mode support `≤ d` `[structural lemma, PROVEN]`
The degree-`d` finite-free / Jensen–Hankel section of `Ξ`: the power-sums `P_k` are **axis-mode** (one prime per
mode), but real-rootedness `⟺` the **Hankel form `H_d=(P_{i+j})` PSD**, and `\det H_j` is a degree-`j` polynomial
in the `P_k` — so the reducibility condition carries **mixed-sign combination modes of support `≤ d`**. "Bounded
degree" = polynomial degree `d` = the maximal combination-mode support. (Full carrier: `finite-free-convolution-flow`.)

## §4 Verdict — reducibility is RH-BLIND (the C5 lead refuted) `[the negative result]`
The edge coboundary norm `N_∞(σ)=Σ_m|ĝ(m)|²/|m·ℓ|²` (explicit-formula coefficient model) **converges iff
`σ>¾`**; the controlling bound is the **elementary integer-gap** `|\log(n_+/n_-)| ≥ |n_+−n_-|/\max`, **not
Baker** (Baker is sharp only for the toy `e^{-ρ|m|}` profile of Lemma R; the physical `∏p^{-2|a|σ}` profile is
ruled by integer gaps). The obstruction in `(½,¾]` is the **consecutive-/balanced-coprime near-resonances
`(M,M−1)`**. `N_∞` is a `𝕋^∞`-**variance** (`L²`) quantity, so by the A1/A2 split it **cannot see RH**, which is
the **single-orbit sign** `\det H_d(θ_{diag}(t)) ≥ 0` (Pólya–Jensen / GORZ). Since `σ=½` sits deep in the
non-reducible zone, **reducibility ⟺ RH is REFUTED.** The reducibility/cocycle framing measures the *average*,
not the single-orbit sign — the wrong handle. **RH content is relocated** to single-orbit positivity of
`\det H_d` (`finite-free-convolution-flow`).

## Door / grade
**BRIDGE** throughout (`𝕋^∞` KAM + Baker + integer-gap + A1/A2 variance). **Not C5** — the C5-as-reducibility
candidate is refuted. Substrate-relevant: Lemma R is the first place Baker is load-bearing, the **#72
"Liouville substitute" / G2 multiplicity estimate** in dynamical dress (a relation among the zeros pushes, via
the Weil explicit formula, to a prime-side `Σm_p\log p≈0` that Baker forbids from being too small).

## Cross-references
- `../5-failed/combination-mode-baker-reducibility.md` — the refuted C5★ lead (full attack history).
- `../1-in-progress/finite-free-convolution-flow.md` — the `σ>¾` threshold to conclusion; the **relocated**
  single-orbit positivity (`\det H_d ≥ 0`) RH target.
- `../2-fully-proven/erosion-cocycle-reducibility.md` — the axis-mode siblings (§59/§60/19a, no Baker).

## Log
- 2026-06-19 (Wheeler) — **created by splitting `combination-mode-baker-reducibility`** (C5★-as-reducibility
  REFUTED → `5-failed`). Banks the proven BRIDGE residue: **Lemma R** (Baker load-bearing for combination-mode
  reducibility, with Liouville counterexample — the first place Baker bites), **Part 1** (the infinite-base /
  unbounded-support no-go: `(\log p)_∞` not polynomially Diophantine, uniform Baker degrades super-exp), the
  **support-≤d** structural lemma, and the **RH-blind verdict** (`σ>¾` threshold integer-gap-driven;
  reducibility⟺RH refuted; RH relocated to single-orbit positivity). Grade BRIDGE.

## Lean anchor — 2026-07-16 (Fable)

Lemma R(i) and the mode-division equation are formalized, unconditional (baseline axioms, no
`sorry`), in `formal/GaloisForLFunctions/HTGeometry/DiagonalModeDivision.lean`:
- `modeFrequency_eq_zero_iff` / `modeFrequency_ne_zero` — `m·ℓ ≠ 0` for every nonzero mode
  (the "ĥ(m) is defined" half of Lemma R), via `ℚ`-linear independence of prime logs.
- `log_diagonalWeightReal`, `diagonalWeight_eq_one_iff` — the diagonal time-one weight of the
  mode lane is `e^{-m·ℓ}`, equal to `1` only at `m = 0`.
- `diagonal_mode_division` — the cohomological division `(δ − id) g = χ_m` solved mode-by-mode
  with explicit divisor `w(m) − 1 ≠ 0`, on the secular Laurent algebra.
- `diagonal_equivariant_kills_mode`, `no_diagonal_equivariant_retraction` — the non-splitting
  consequence, through the shared weld mechanism (`equivariant_linear_kills_scaled`).
NOT formalized (and not claimable unconditionally in Lean today): Lemma R(ii) — the
Baker–Wüstholz effective lower bound `|m·ℓ| ≥ γ·H(m)^{-κ}` — and the Part-1 pigeonhole no-go;
these remain classical-import / paper-tier. The formalized floor is exactly the
unique-factorization half the card marks as (i).

## Lean anchor — 2026-08-30 (Part 1 closed)

The **Part-1 pigeonhole no-go** listed above as "NOT formalized" is now Lean-proved,
unconditionally and axiom-clean, in
`formal/GaloisForLFunctions/HTGeometry/DirichletBoxLinearForm.lean`:

- `sub_le_of_min_floor_eq` — two reals in `[0, K·b]` with the same clamped box index differ by at
  most `b` (the box-principle estimate, with the top box closed);
- **`exists_small_linear_form`** — Dirichlet's box principle for a nonnegative linear form: for every
  `s ≥ 1`, every `ℓ : Fin s → ℝ≥0` and every `N ≥ 1` there is a **nonzero** integer mode `m` with
  `|m_i| ≤ N` and

  `|∑ m_i ℓ_i| ≤ N·(∑ ℓ_i) / ((N+1)^s − 1)`;

- **`exists_small_mode_of_subexponential`** — if the partial sums `∑_{i<s} ℓ_i` are
  `o(3^s)` then modes with entries bounded by `2` make the form arbitrarily small;
- **`not_polynomially_diophantine`** — the card's statement: for every `γ > 0` and every exponent
  `κ` there is a nonzero mode with `H(m) = 3` and `|m·ℓ| < γ·3^{-κ}`, so no fixed-exponent
  Diophantine condition can hold once the support size is free.  This is precisely
  "`(log p)_∞` is not polynomially Diophantine over unbounded-support modes", with the
  subexponential growth of `∑_{i<s} log p_i` supplied as the hypothesis on the frequency vector.

Still not formalized: **Lemma R(ii)** — the effective Baker–Wüstholz lower bound
`|m·ℓ| ≥ γ·H(m)^{-κ}` for the prime frequency.  That is the single remaining classical import for
this card; the corpus owns qualitative Baker only.

### §3 and §4 are also closed (2026-08-30)

- `HTGeometry/HankelDetTotalDegree.lean` — **`totalDegree_hankelDet_le`**: the determinant of the
  `d × d` Hankel matrix in the indeterminates `P_k` has total degree at most `d`.  This is §3: every
  monomial of the reducibility condition carries combination-mode support at most `d`, so bounded
  degree bounds the support.
- `HTGeometry/IntegerLogGap.lean` — `one_sub_inv_le_log`, `gap_div_le_log_div` and
  **`gap_div_le_abs_log_div`**: for distinct positive integers,
  `|a − b| / max(a,b) ≤ |log(a/b)|`.  This is the elementary integer-gap bound that §4 identifies as
  the controlling estimate for the edge coboundary norm (the place where Baker is *not* the
  operative input).

**Card status.**  Lemma R(i), §2 Part 1, §3 and §4's controlling bound are all formalized
unconditionally.  The one remaining classical import is **Lemma R(ii)**, the effective
Baker–Wüstholz lower bound for a fixed finite set of prime logarithms.  Note that the elementary
bound `|∑ m_p log p| ≥ (∏ p)^{−H(m)}` available from `gap_div_le_abs_log_div` is exponential in
`H(m)` and therefore genuinely insufficient for R(ii), which needs the polynomial `H(m)^{−κ}` —
this is exactly the sense in which the card says Baker is load-bearing.

## Lean anchor — 2026-08-30 (both halves of the L² dichotomy)

Lemma R's *consequences* — the two directions the card actually uses — are now Lean-proved,
unconditionally and axiom-clean.  Only the Baker input itself remains.

`formal/GaloisForLFunctions/HTGeometry/CombinationModeDiophantineDivisor.lean`:

- `modeNorm`, `modeHeight` (`H(m) = max(3, maxᵢ|mᵢ|)`), `modeForm` — the mode data of the card;
- `summable_prod_pi` — a finite product of summable nonnegative weights is summable on the integer
  lattice `ℤ^s` (`Fin.consEquiv` induction plus `Summable.mul_of_nonneg`);
- `three_add_sum_le_prod` — `3 + Σ aᵢ ≤ ∏ (3 + aᵢ)` on a nonempty finset of nonnegative reals, the
  factorisation that turns the height weight into a product;
- `summable_modeWeight` — `Σ_m (3 + |m|₁)^K e^{−2ρ|m|₁} < ∞`;
- **`summable_modeDivisor_of_diophantine`** — the positive half of Lemma R: if
  `|m·ℓ| ≥ γ·H(m)^{−κ}` for every nonzero mode and `|ĝ(m)| ≤ e^{−ρ|m|₁}`, then
  `Σ_{m ≠ 0} |ĝ(m)|²/(m·ℓ)² < ∞`, i.e. the mode-divided solution is in `L²` and the cocycle is
  reducible.

`formal/GaloisForLFunctions/HTGeometry/LiouvilleFrequencyNonReducible.lean`:

- `gapExp` (`a₀ = 2`, `a_{k+1} = a_k + 1 + 16^{a_k}`), `superLiouville` `α = Σ 2^{−a_k}`,
  `qDen`/`pNum` its canonical approximations, `approx_pos` and **`approx_upper`**
  (`0 < q_K α − p_K ≤ 2^{−16^{a_K}}`);
- `superLiouville_irrational` — irrationality, by the elementary "a positive integer is at least
  one" contradiction against the approximation rate;
- `exp_le_two_pow` — `exp(4·4ⁿ) ≤ 2^{16ⁿ}` for `n ≥ 2`, the inequality that makes the gap beat the
  square of the mode size;
- **`abs_modeForm_liouvilleMode_le`** — `|m_K·(1,α)| ≤ exp(−|m_K|₁²)` for the resonant modes
  `m_K = (−p_K, q_K)`;
- **`exists_liouville_frequency`** — a frequency vector whose linear form never vanishes on a
  nonzero mode yet is smaller than `exp(−|m|²)` on modes of arbitrarily large size;
- **`not_summable_liouvilleDivisor`** — for every decay rate `ρ > 0` the divided series
  `Σ_{m≠0} e^{−2ρ|m|₁}/(m·ω)²` has unbounded terms and is therefore not summable: `h ∉ L²`, the
  cocycle is **not** reducible.

**Card status.**  Lemma R(i), the `L²` sufficiency, the Liouville counterexample, §2 Part 1, §3 and
§4's controlling bound are all formalized unconditionally.  The single remaining classical import is
**Lemma R(ii)** — the effective Baker–Wüstholz bound `|m·ℓ| ≥ γ·H(m)^{−κ}` for a fixed finite set of
prime logarithms — which is exactly the hypothesis of `summable_modeDivisor_of_diophantine`.  Its
formalization is the separate project
`docs/drafts/pipeline/1-in-progress/effective-baker-matveev-linear-forms.md`; when that lands, the
prime-frequency instance of Lemma R closes by direct application and this card moves to stage 3.
