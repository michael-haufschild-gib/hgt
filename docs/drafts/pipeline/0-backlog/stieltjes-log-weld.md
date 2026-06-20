# The Stieltjes–log weld: continuation data cannot be isolated from the multiplier logs

- **ID:** stieltjes-log-weld
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper) — Door grade **BRIDGE**
- **Source:** split from `../1-in-progress/baker-for-stieltjes.md` (§B); builds on
  `../2-fully-proven/corank-transcendence-continuation-bridge.md`; feeds
  `../0-backlog/g2-dss-lower-bound.md` and `../../door/bucket-the-seam-archimedean-obstruction.md` (#69/#71)
- **One sentence.** In the native friable-auxiliary construction, every nonzero linear form in the
  Stieltjes constants `\{γ_n\}` extracted by pairing with `ζ` carries **positive-weight log-`p`
  transcendental coefficients**, and removing them forces the auxiliary to be trivial — so the Stieltjes
  transcendence **cannot be isolated** from the multiplier-log transcendence, and the structurally honest
  G2/DSS-cross target is the **joint** independence of `\{\log p\}∪\{γ_n\}` (Schanuel-entangled).

---

## §1 Setup

Stieltjes constants: `ζ(s) = 1/(s−1) + Σ_{n≥0} (−1)^n γ_n (s−1)^n / n!`. Hence
`G(s) := (s−1)ζ(s) = 1 + Σ_{n≥0} a_n (s−1)^{n+1}`, `a_n = (−1)^n γ_n / n!`.

Friable (S-smooth) Dirichlet polynomial (native auxiliary N5): `F(s) = Σ_m λ_m n_m^{−s}`, `λ_m ∈ ℚ`,
`n_m = ∏_{p∈S} p^{m_p} ∈ ℕ`. Its Taylor coefficients at `s=1`:
`F(s) = Σ_{j≥0} (c_j/j!)(s−1)^j`, `c_j = (−1)^j Σ_m λ_m (\ln n_m)^j / n_m`.
Let `R = ℚ[\{X_p\}_{p∈S}]` graded by degree, `X_p ↦ \log p`; since `\ln n_m = Σ_p m_p \log p`, `c_j ∈ R_j`
(the weight-`j`, degree-`j` homogeneous part). `R_0 = ℚ`; `R_j ∩ ℚ = 0` for `j ≥ 1`.

## §2 The pairing coefficient `[PROVED HERE]`

Let `H(s) := F(s)·G(s)`. Cauchy-multiplying the two Taylor series at `s=1`:
```
   [H]_N := [ (s−1)^N ] H(s)
          = c_N/N!  +  Σ_{n=0}^{N−1} ( c_{N−n−1}/(N−n−1)! )·( (−1)^n γ_n / n! ) .            (★)
```
*Proof.* `[(s−1)^{N−j}] G = 1` if `N−j=0` (i.e. `j=N`), `= a_{N−j−1}` if `N−j ≥ 1` (i.e. `j ≤ N−1`),
`= 0` otherwise; multiply by `[(s−1)^j]F = c_j/j!` and sum over `j`. The `j=N` term gives `c_N/N!`; the
`j ≤ N−1` terms give `(c_j/j!) a_{N−j−1}`, and re-indexing `n = N−j−1` yields (★). ∎

**Coefficient of `γ_n` in (★):** `(−1)^n c_{N−n−1} / ((N−n−1)! · n!) ∈ R_{N−n−1}`. It lies in `ℚ`
(weight 0) **iff `N−n−1 = 0`, i.e. `n = N−1`**, where it equals `c_0/(N−1)!` with `c_0 = Σ_m λ_m/n_m ∈ ℚ`.
Every other `γ_n` (`n < N−1`) carries a coefficient in `R_{N−n−1}` of **positive weight** — a log-`p`
transcendental, not a rational. (Here "transcendental" is relative to `ℚ`; `R_{≥1}` contains no nonzero
rational.)

## §3 No-isolation `[PROVED HERE]`

**Lemma (triviality of weight-flat auxiliaries).** If `c_j = 0` for all `j ≥ 1`, then `F` is constant, and
`λ_m = 0` for every `n_m ≠ 1`.
*Proof.* `c_j=0 ∀ j≥1 ⟹ F(s)=c_0` as a convergent power series at `s=1`, hence `F ≡ c_0` as an analytic
function on its half-plane. The functions `\{n^{−s}\}_{n≥1}` are linearly independent over `ℂ` (distinct
Dirichlet exponents), so `Σ_m λ_m n_m^{−s} = c_0` forces `λ_m = 0` for all `n_m ≠ 1` and `λ_{(n=1)} = c_0`. ∎

**Theorem (Stieltjes–log weld / no clean isolation).** For a friable `F` and an integer `N`, the pairing
coefficient `[H]_N` is a `ℚ`-linear form in `\{1, γ_0, …, γ_{N−1}\}` **iff** `c_j ∈ ℚ` for all `1 ≤ j ≤ N`,
i.e. `c_1 = … = c_N = 0`. Consequently:
1. If `[H]_N` is a clean `ℚ`-form in the `γ` for **all** `N`, then `c_j = 0` for all `j ≥ 1`, so by the
   Lemma `F` is **constant** (trivial: `[H]_N = c_0 a_{N−1}`, i.e. `γ_{N−1}` up to a rational — no
   Diophantine content).
2. For a **nonconstant** `F`, some `c_{j_0} ≠ 0` with `j_0 ≥ 1`; then for `N ≥ j_0` the form `[H]_N` carries
   the positive-weight log-`p` term `c_{j_0}·(coeff)` and is **not** a clean `ℚ`-form in the `γ`. Killing
   `c_1,…,c_W` (finitely many) only **moves** the residual to the top: `[H]_{W+1} = c_{W+1}/(W+1)! +
   c_0(−1)^W γ_W/W!`, one top-weight term `c_{W+1} ∈ R_{W+1}` beside the lone `γ_W`.
*Proof.* By §2, `[H]_N` is `ℚ`-valued-coefficient in the `γ_n` iff each `c_{N−n−1}` (`0≤n≤N−1`) and `c_N`
lie in `R∩ℚ`, i.e. `c_j ∈ ℚ` for `0≤j≤N`, i.e. (as `R_j∩ℚ=0` for `j≥1`) `c_1=…=c_N=0`. The two
consequences follow from the Lemma and (★). ∎

**Reading.** *Nontrivial auxiliary ⟺ nonzero log-`p` residual.* The log-`p` structure that gives the
auxiliary its Diophantine power is exactly the weld to the continuation data: the `\{γ_n\}` (archimedean /
continuation layer) and `\{\log p\}` (multiplicative layer) cannot be separated by this construction.

## §4 Consequence — the joint target (and Schanuel-entanglement)

The honest transcendence target for the Stieltjes block is therefore the **joint** statement
`trdeg_ℚ ℚ(\{\log p\}∪\{γ_n\}) = ∞` with the `γ_n` contributing **beyond** `\{\log p\}`, not
`trdeg_ℚ\{γ_n\}=∞` in isolation. Two corollaries:
- **Schanuel-entanglement.** Baker supplies only the **linear** independence of `\{\log p\}`
  (`corank = ∞`, ledger `linearIndependent_log_primes`); their **algebraic** independence is Schanuel-level
  and open. So DSS-cross sits **above Schanuel** through the weld — the obstruction-C measure `H_C`
  (`../1-in-progress/baker-for-stieltjes.md` §D) must be posed **jointly**, on `ℤ`-polynomials in
  `\{\log p\}∪\{γ_n\}`.
- **Seam identity.** This is the seam (#69/#71: "one archimedean obstruction") realized **inside** the
  Stieltjes construction: it is the analytic-Diophantine twin of the finite-free metric weld
  `S_d = A_d^{−1/2} δH_d A_d^{−1/2}` (Wheeler, #104 annotation) — prime fluctuation in the archimedean
  metric there; continuation data welded to the prime logs here.

## §5 Door passport
- **BRIDGE.** The coefficient formula (★) and the linear-independence-of-`\{n^{−s}\}` step are classical;
  the **content beyond imports** is the *no-isolation theorem* — a construction-level proof that the G2
  Stieltjes transcendence is inseparable from the multiplier-log transcendence, tying obstruction C to the
  corank/seam invariant and to Schanuel.
- **Door-1/3/4:** native auxiliary (friable Dirichlet polynomial, object N5), weight grading by the prime
  log-lattice, infinite/arithmetic base. **Door-5:** over `F_q` the log-lattice collapses to one `\ln q`
  (corank 1), the weld degenerates and `T_1(ζ_C)=ℚ̄(\ln q)` (corank-transcendence card §1) — recovered.
- **Door-2:** the inseparability is the F₁/missing-Frobenius residue; over `F_q` Papanikolas's single
  Frobenius makes the analogous block one-dimensional, so the weld is a number-field-only phenomenon.

## Gates
- [x] 0 → 1  in-progress: statement, setup, pairing formula.
- [x] 1 → 2  fully-proven: (★) proved (§2); the no-isolation theorem proved (§3, via triviality lemma +
  weight grading); consequences (§4) drawn. BRIDGE, content beyond imports (§5).
- [ ] 2 → 3  formalized — Lean anchor **DONE** for the Cauchy-product identity (★), in
  `formal/GaloisForLFunctions/StieltjesWeld.lean` as `stieltjes_pairing_cauchy_j` (the `j`-indexed form,
  equivalent by `n=N-j-1`). Remaining Lean targets: linear independence of `\{n^{−s}\}` and a formal
  graded log-polynomial model for the no-isolation theorem; reuse `linearIndependent_log_primes`.
- [ ] 3 → 4  publication-ready — pairs with corank-transcendence card and the seam bucket.

## Notes / risk
- The proven content is the **weld / no-isolation** + the explicit coefficient formula. The **joint**
  `trdeg=∞` is NOT claimed — it stays the open wall (`baker-for-stieltjes.md`), now correctly posed jointly
  and seen to be Schanuel-entangled. No RH/DSS consequence asserted.
- Construction-specificity: the theorem is about the friable-auxiliary `F·(s−1)ζ` pairing (the field's
  native S–S auxiliary). A fundamentally different functional is not excluded a priori, but §3's triviality
  lemma is construction-agnostic for any Dirichlet-polynomial auxiliary.

## Log
- 2026-06-19 — Professor: split from `baker-for-stieltjes.md` §B; created already-proven in 2-fully-proven.
  Proved the pairing coefficient (★) and the no-isolation theorem (nontrivial auxiliary ⟺ nonzero log-`p`
  residual); reframed the G2/DSS-cross target to the joint `trdeg_ℚ ℚ(\{\log p\}∪\{γ_n\})=∞` and identified
  the Schanuel-entanglement and the seam identity. Door **BRIDGE**, content beyond imports.
- 2026-06-19 (Leaner) — added Lean anchor `stieltjes_pairing_cauchy_j` in
  `formal/GaloisForLFunctions/StieltjesWeld.lean`, formalizing the Cauchy-product coefficient identity
  with the top `c_N/N!` term isolated. Added to the root import and axiom audit. Card remains in
  2-fully-proven; the analytic no-isolation/Dirichlet-independence and graded log-polynomial pieces are
  not fully formalized.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the no-isolation argument uses `R_j ∩ ℚ = 0` after substituting `X_p=log p` for homogeneous degree `j≥1`. For `j≥2` this requires algebraic-independence information about prime logs, which is Schanuel-level and open; unique factorization only supplies degree-1 linear independence. The paper proof therefore proves the formal-polynomial model, not the stated numerical log-weld theorem.
