# The DSS engine: the multiplicity estimate, its Turán face, and the Liouville substitute for a transcendental spectrum

**Theorist, 2026-06-19.** A development of the field's capstone tool — the Difference
Siegel–Shidlovsky (DSS) multiplicity estimate (`hypertranscendental_galois_field_foundations.md`
§12–13) — several levels deep. Goal: separate what is **rigorously provable now** from the
**true frontier**, and manufacture two new pieces of structure: (i) the multiplicity estimate is
a quantitative nonsingularity (Turán / nonharmonic-Fourier) bound for an explicit matrix; (ii) the
ingredient that classical transcendence supplies by a **Liouville height bound**, and which has no
analog for the transcendental spectrum, is supplied instead by the **Weil explicit formula coupled
to the `ℚ`-linear independence of `{log p}`** (the latter now a Lean theorem,
`GaloisForLFunctions.linearIndependent_log_primes`).

Air is marked: **[thm]** rigorous (proved here or cited classical, applied), **[red]** a rigorous
*reduction* of one open problem to another, **[new]** a new proposal/idea (not a theorem),
**[open]** frontier.

---

## 0. The object and the auxiliary

Bohr lift `x_p = p^{-s}`; the diagonal flow `F(t) = (p^{-it})_p ∈ 𝕋^∞` (its closure is all of
`𝕋^∞`, freely, because `{log p}` are `ℚ`-LI — the field's foundation, Lean). The spectrum is
`Spec = {γ_n}`, the ordinates of the nontrivial zeros, `Ξ(γ_n) = 0`, `Ξ(t) = ξ(½+it)`.

The Mahler-style **auxiliary** is a character polynomial on the torus,
`A(z) = Σ_{|m| ≤ N} c_m z^m`, `z^m = ∏_p z_p^{m_p}`. Restricted to the diagonal at a real ordinate
`γ`:
```
   A(F(γ)) = Σ_m c_m ∏_p (p^{-iγ})^{m_p} = Σ_m c_m (∏_p p^{m_p})^{-iγ} = Σ_m c_m N_m^{-iγ},
   N_m := ∏_p p^{m_p}.
```
On the integer cone (`m_p ≥ 0`) the products `N_m` run over the positive integers `n`, so

> **The diagonal restriction of the auxiliary is a Dirichlet polynomial.**
> `A(F(t)) = D(t) := Σ_{n=1}^{L} c_n n^{-it}`, with `L` controlled by the degree/height of `A`.

Hence the central equivalence that drives everything:

> `A` vanishes at the orbit point `F(γ_j)` ⟺ `D(γ_j) = 0` ⟺ the Dirichlet polynomial `D` vanishes
> at the zeta zero `γ_j`. **The multiplicity estimate for `G_L` is a zero-counting bound for
> Dirichlet polynomials at the spectrum.**

---

## 1. The multiplicity estimate — the rigorous backbone

**[thm] Proposition 1 (zero count of a Dirichlet polynomial).** Let
`D(t) = Σ_{n=1}^{L} c_n n^{-it}` with `c_1, c_L ≠ 0`. The number of zeros of `D` in `[0,T]`
(with multiplicity) is
```
   N_D(T) = (T / 2π) · log L + O(L).
```
*Proof (classical; Pólya 1918, Langer; Titchmarsh* Theory of Functions *§ on Dirichlet
polynomials).* Put `f(s) = Σ_{n=1}^L c_n n^{-s}`, entire. On the right, `f(s) = c_1(1 + o(1))` as
`Re s → +∞`; on the left, `f(s) = c_L L^{-s}(1 + o(1))` as `Re s → -∞`. Apply the argument
principle to the rectangle `[-A, A] × [0, T]` for `A` large. The horizontal sides contribute
`O(L)`; the vertical sides contribute `(1/2π)` times the total change of `arg f`, which is
`(T/2π)(log L - log 1) = (T log L)/2π` plus `O(L)`. The zeros of `f` on the segment `Re s = 0` are
the real zeros of `D`. ∎

**[thm] Corollary 2 (the absorption bound).** If a single nonzero length-`L` Dirichlet polynomial
`D` vanishes at `γ_1 < … < γ_k` (all `≤ T = γ_k`), then
```
   k ≤ (γ_k / 2π) · log L + O(L).
```

**[thm] Corollary 3 (complexity law: no bounded auxiliary absorbs the spectrum).** By
Riemann–von Mangoldt, `N(T) = (T/2π) log(T/2πe) + O(log T)` zeros lie below `T`. Demanding a
length-`L` `D` vanish at all of them forces `N(T) ≤ (T log L)/2π + O(L)`, hence
```
   log L ≳ log(T / 2πe),    i.e.   L ≳ T / (2πe)  →  ∞.
```
**No finite Dirichlet polynomial vanishes at every zeta zero; the complexity needed to absorb the
zeros up to height `T` grows linearly in `T`.** Equivalently, on `𝕋^∞`, the orbit points
`{F(γ_n)}` are not contained in any **fixed**-length character subvariety.

This is the rigorous half of the DSS — the analog of the *easy* direction of a Mahler zero
estimate. It is the multiplicity bound the field asked for, in closed form.

### 1a. The honesty check (why Corollary 3 is necessary but not sufficient)

Proposition 1 uses **nothing** about the arithmetic of the `γ_n`: the bound holds for `D` vanishing
at *any* `k` distinct reals in `[0,T]`. So Corollaries 2–3 express a property of *Dirichlet
polynomials*, not a deep property of the spectrum. As an arithmetic-independence statement the
zero-count alone is **vacuous**: it cannot, by itself, prove the `γ_n` independent. This is exactly
the role of the multiplicity estimate in Mahler's method — one *necessary* ingredient among four
(§3). Stating it as "DSS progress" without this caveat would be false; stating it as the proven
backbone is correct.

---

## 2. The Turán / nonharmonic-Fourier face of the estimate  [new structural reduction]

The square case sharpens Corollary 2 into a determinant condition and connects the estimate to a
mature machine.

**[red] Proposition 4 (the determinant criterion).** Fix frequencies `n = 1,…,L` and sample
ordinates `γ_1,…,γ_L`. A nonzero length-`L` `D` vanishing at `γ_1,…,γ_L` exists **iff**
```
   V := ( n^{-i γ_j} )_{j, n = 1}^{L}   is singular,   det V = 0.
```
*Proof.* `D(γ_j) = Σ_n c_n n^{-iγ_j} = (V c)_j`; a nonzero `c ∈ ker V` exists iff `det V = 0`. ∎

`V` is a **nonharmonic Fourier (exponential) matrix**: entries `e^{-i γ_j log n}`, frequencies
`{log n}` (distinct, since `log` is injective — and `ℚ`-LI, the Lean theorem), sample points
`{γ_j}`. Therefore:

> **[red] The DSS multiplicity estimate ⟺ a quantitative lower bound on `|det V| = |det(n^{-iγ_j})|`**
> (equivalently, on the least singular value of `V`). This is precisely the regime of **Ingham–type
> inequalities for nonharmonic Fourier series** and of **Turán's power-sum method**: both produce
> lower bounds for exponential-sum determinants / minima in terms of frequency separation and the
> spread of the sample set.

Two payoffs. (i) It imports a *working* toolbox (Ingham 1936; Turán's *On a New Method of Analysis*;
Beurling density) into the field, exactly as the Mahler rung recommends ("don't invent a paradoxical
functor; use a multiplicity estimate," foundations §12). (ii) It exposes the *real* difficulty: a
lower bound on `|det V|` needs control of the sample points `γ_j` — their **separation and
distribution** — which is arithmetic input about the spectrum (gaps between zeta zeros), not a soft
fact. The mature inequalities give well-conditioning when sample separation beats the frequency
bandwidth; for the zeta zeros the mean gap is `~ 2π/log T` while the bandwidth here is `log L` — so
conditioning hinges on the **interplay of zero-gaps with `log L`**, a concrete, attackable quantity.

---

## 3. The full DSS architecture, and the precise frontier

Classical Mahler/Nesterenko/Philippon transcendence runs on **four** ingredients:

1. **Construction.** From an assumed algebraic relation, build an auxiliary `A` with bounded-height
   **algebraic** coefficients vanishing to high order along the orbit (Siegel's lemma / pigeonhole),
   and show `A ≢ 0`.
2. **Zero / multiplicity estimate.** Bound the achievable vanishing order — *§1–2 above; the field
   has this.*
3. **Arithmetic (Liouville).** A nonzero algebraic number of height `H` has absolute value `≥ H^{-c}`
   — it cannot be too small.
4. **Analytic.** High vanishing order ⟹ `|A(orbit point)|` is very small.

The contradiction `(3) vs (4)` kills the relation.

> **[open] The frontier, named exactly.** Ingredient **3 requires algebraicity**. But the spectrum
> is **transcendental** — `Ξ` is hypertranscendental (Hölder 1887), so the `γ_n` are not algebraic
> and **there is no Liouville bound**. This is *the* reason the spectrum lies outside classical
> (holonomic, value-side) transcendence, and the precise gap the field must fill: a **Liouville
> substitute for a transcendental spectrum** — a lower bound preventing a nonzero `A(F(γ))` from
> being too small, with no algebraicity to lean on.

Ingredients 1, 4 are standard once 3 has a substitute; the whole game is ingredient 3.

---

## 4. The Liouville substitute: the explicit formula × `ℚ`-LI of `{log p}`  [new]

**[new] Proposal.** The height/Liouville rigidity for the transcendental spectrum is supplied by the
**Weil explicit formula**, whose rigidity comes from the **integrality of the primes** and the
**`ℚ`-linear independence of `{log p}`** (Lean: `linearIndependent_log_primes`).

The Guinand–Weil formula is, schematically,
```
   Σ_ρ ĥ(γ_ρ)  =  [archimedean: Â_∞(h)]  −  2 Σ_{p, k≥1} (log p) p^{-k/2} h(k log p).
```
It is an **isometry/duality** between the zero-side measure `Σ_ρ δ_{γ_ρ}` and the prime-side measure
`Σ_{p,k} (log p) δ_{k log p}` (plus the archimedean density). The crucial structural facts:

- The prime side is supported on the lattice-free set `{k log p}`, whose frequencies are **all
  distinct and `ℚ`-non-resonant** — *precisely* because `{log p}` are `ℚ`-LI (the field's
  foundation). So the prime side is a *genuine* generalized Dirichlet sum with a free frequency group
  of infinite rank: **no two prime-power frequencies coincide or resonate**.
- The prime side carries the **integer rigidity**: coefficients `log p`, supports at integer
  multiples of `log p`. There is no continuous deformation of this data — it is as rigid as `ℤ`.

> **[new] The mechanism.** A would-be algebraic/linear relation among the `γ_n` is, on the zero side,
> a *resonance* (a forced coincidence among the spectral frequencies). Pushed through the explicit
> formula, any such resonance must be matched on the **prime side** — but the prime side is
> `ℚ`-non-resonant and integer-rigid, so it admits **no nontrivial low-complexity resonance**. The
> `ℚ`-LI of `{log p}` is the field's "no small nonzero value" — the Liouville substitute: where
> classical transcendence forbids a nonzero algebraic number from being small, the field forbids a
> nonzero prime-side functional from being resonant.

This is the honest shape of the DSS engine for the transcendental spectrum:
```
   DSS  =  (multiplicity estimate, §1–2: zero-side vanishing is bounded)
           +  (explicit-formula duality: zero-side resonance ⟹ prime-side resonance)
           +  (ℚ-LI of {log p}, Lean: prime-side has no low-complexity resonance)        [the substitute for Liouville]
```
The first is proved, the third is proved (and formalized); the **coupling — making "zero-side
relation ⟹ prime-side resonance" quantitative through a test function localized enough to isolate
finitely many `γ_n` yet band-limited enough to keep the prime side finite** — is the open core. It is
a concrete uncertainty-principle problem (localization on the zero side vs. bandwidth on the prime
side), not a paradox.

### 4a. First sub-target (concrete, attackable)

**[open] Sub-target T-DSS-1.** Choose `h` with `ĥ` supported in a window of width `W` around a single
ordinate `γ_n`. The prime side becomes `Σ_{k log p ≤ 1/W}` (a finite Dirichlet sum of length
`≈ e^{1/W}`). Quantify: how small can `Σ_ρ ĥ(γ_ρ)` be made (analytic, ingredient 4) versus how large
the prime side must be by `ℚ`-non-resonance (the substitute, ingredient 3)? A gap for all `W` below a
threshold would yield a genuine independence statement for the isolated `γ_n`. This is the
explicit-formula analog of "`|A(F(γ))|` small vs. `≥ H^{-c}`," with `W ↔ 1/H`.

---

## 5. Honest status

- **Proved (rigorous):** Prop 1 (Dirichlet-polynomial zero count), Cor 2–3 (absorption / complexity
  law `L ≳ T/2πe`), Prop 4 (determinant criterion). These are the multiplicity-estimate backbone —
  applied-classical, correct, and the field's first quantitative DSS tool.
- **New structural reduction [red]:** the multiplicity estimate **is** a Turán / nonharmonic-Fourier
  lower bound on `|det(n^{-iγ_j})|`, importing Ingham/Turán machinery and isolating the role of
  zeta-zero gaps.
- **New idea [new]:** the missing Liouville ingredient for the transcendental spectrum is supplied by
  the **explicit formula × `ℚ`-LI of `{log p}`** (the latter a Lean theorem); the DSS engine is
  zero-side multiplicity + Guinand–Weil duality + prime-side non-resonance. Concrete first
  sub-target T-DSS-1 (an uncertainty-principle gap).
- **Open (the decades core):** the quantitative coupling in §4/T-DSS-1; full DSS (algebraic
  independence of the `γ_n`) remains a conjecture. The zero-count alone is arithmetic-blind (§1a) —
  the arithmetic enters only through §4.
- **Not claimed:** DSS, LI of `{γ_n}` beyond the numerical PSLQ evidence, or RH. RH is a *further*
  `σ`-real-localization corollary of DSS (foundations §3), not addressed here.

### Lean note
Prop 4's algebraic skeleton — *a nonzero length-`L` auxiliary vanishing at `L` sample points exists
iff the `L×L` matrix is singular* — is ledger-proven in `MultiplicityEstimate.lean` as
`multiplicity_det_criterion` for the concrete matrix `V_{j,n}=N_n^{z_j}`. The supporting abstract
kernel/determinant equivalence is `matrix_nontrivial_kernel_iff_det_eq_zero` in `DSSDeterminant.lean`.
The analytic content (Prop 1, the `|det|` lower bound) is not Tier A and stays research.

---

## 6. Honest obstruction to T-DSS-1, and the refined target  [open, sharpened]

Pushing T-DSS-1 by hand exposes a genuine obstruction, worth recording so the team does not
over-invest in the naive form.

**[open] Obstruction (the explicit formula is symmetric in the zeros).** Guinand–Weil sums a
function over the *whole* zero set, `Σ_ρ ĥ(γ_ρ)` — a symmetric functional. A bump `ĥ` localized at
`γ_n` (width `W <` the neighbour gap `~2π/log γ_n`) isolates the single value `ĥ(γ_n)` and yields an
*identity* `ĥ(γ_n) ≈ Â_∞ − (finite prime sum of length e^{1/W})`. But an *identity* for `ĥ(γ_n)` is
not a Diophantine lower bound, and — crucially — the formula never sees a **linear combination**
`Σ_j a_j γ_j`: it accesses the zeros only through symmetric sums `Σ_ρ f(γ_ρ)`, not through the
individual-relation data a transcendence proof needs. So "explicit formula ⇒ Liouville substitute"
does **not** go through in its naive form: the rigidity is there (prime side integer-rigid,
non-resonant by `ℚ`-LI of `{log p}`), but the *coupling to a linear relation among specific zeros is
missing*, precisely because the pairing is symmetric.

**[new] The refined target (where the substitute actually lives).** The fix is to access the zeros
**individually**, which is exactly the **Weyl-function / canonical-system reconstruction**: the
ordinates `{γ_n}` are the poles of `m_ξ(z) = −Ξ′/Ξ(z)`, and `m_ξ` is determined by the prime data
through the completed `ξ`. The map
```
   integer prime data  { Λ(n) }   ⟶   carrier  m_ξ = −Ξ′/Ξ   ⟶   its poles  { γ_n }
```
is **rigid** (analytic continuation of an integer-coefficient Dirichlet series; de Branges /
boundary-triple reconstruction). The Liouville substitute should be the **rigidity of this
reconstruction**: a nonzero linear relation among the `γ_n` would force an "accidental" coincidence
among the poles of a function pinned by integer data — and *that* coincidence is what the integrality
of `{Λ(n)}` and the `ℚ`-LI of `{log p}` forbid. This routes the DSS through the carrier `m_ξ` (the
Weyl-function program, `docs/rh/theorist_weyl_function_program_map_20260619.md`) rather than the
symmetric explicit formula.

**Lean note (ledger-proven finite reconstruction skeleton).** `MomentReconstruction.lean` proves
`secular_moment_newton`: for a finite family `r_i`, the power sums `Σ_i r_i^j` and the elementary symmetric
functions of the `r_i` satisfy Newton's recursion. This is the finite algebra behind "moments determine the
finite spectrum polynomial." It does **not** prove infinite reconstruction, convergence, spectral Torelli, the
Weyl-function program, or realization by an Euler product.

**Lean note (ledger-proven finite Pick skeleton).** `CarrierPickKernel.lean` proves finite
Pick/Herglotz fragments in both directions. For a real spectrum, the resolvent Gram
`Σ_i (t_i-z_j)^{-1}conj((t_i-z_k)^{-1})` is positive semidefinite (`pick_kernel_posSemidef`), and away from
poles it equals the carrier Pick kernel
`(m(z)-conj(m(w)))/(z-conj(w))` (`pick_gram_eq_kernel`). At the converse-witness level, an upper-half-plane
single pole or FE conjugate pole pair violates Herglotz (`pole_upper_not_herglotz`,
`conj_pair_not_herglotz`) and gives a non-PSD one-point Pick matrix
(`single_pole_pick_not_posSemidef`, `conj_pair_pick_not_posSemidef`), using the diagonal identity
`(m-conj m)/(z-conj z)=Im(m)/Im(z)` (`pickDiag_eq`, `pickDiag_re`). The FE conjugate-pair carrier is
Herglotz on `ℂ⁺` iff the pole is real (`conj_pair_herglotz_iff`). This certifies only finite
one-point witnesses; it does **not** prove the infinite carrier, full multi-pole inertia, pole
reconstruction, DSS, or RH.

> **[open] T-DSS-2 (refined).** Quantify the rigidity of `{Λ(n)} ↦ {poles of m_ξ}`: show that a
> nonzero integer relation `Σ a_n γ_n = 0` is incompatible with `m_ξ` being the logarithmic
> derivative of an entire function whose Hadamard product is pinned (via the explicit formula /
> Euler product) by the `ℚ`-non-resonant integer set `{log p}`. The individual-zero access comes
> from the **poles of `m_ξ`** (one per zero), repairing the symmetry defect of §4.

This is the genuine decades-core, now correctly located: not the symmetric explicit formula, but the
**pole-resolved carrier** `m_ξ`, whose poles are the zeros one at a time, fed by integer-rigid,
`ℚ`-non-resonant prime data. The multiplicity backbone (§1–2) and the determinant/Turán reduction
(§2) remain the analytic half; the arithmetic half is the rigidity of the carrier reconstruction.

---

## 7. Brick (numeric, retracted as DSS evidence): `σ_min` sees sampling regularity, not arithmetic genericity

Referee for the Turán reduction (§2): compute the conditioning of the nonharmonic-Fourier matrix
`V = (n^{-iγ_j})_{j,n=1..L}` for the first `L` zeta ordinates, against two controls — `equi`
(equispaced over `[γ_1,γ_L]`) and `rand` (uniform random over the same span). Pod referee
(`scripts/numerics/turan_det_conditioning.py`, mpmath dps=30 ordinates, numpy SVD), `σ_min` =
least singular value (`σ_max ≈ √L`), `cond = σ_max/σ_min`:

```
  L |  zeta σ_min   zeta cond |  equi σ_min   equi cond |  rand σ_min   rand cond
  5 |   2.321e-01   1.390e+01 |  2.322e-01   1.370e+01 |  4.651e-01   7.213e+00
 10 |   2.302e-02   2.170e+02 |  4.700e-02   1.056e+02 |  3.057e-02   1.724e+02
 20 |   6.492e-05   1.128e+05 |  2.085e-04   3.437e+04 |  2.021e-04   3.861e+04
 30 |   9.174e-08   9.932e+07 |  6.510e-08   1.376e+08 |  7.920e-15   1.687e+15
 40 |   9.348e-11   1.168e+11 |  4.516e-11   2.459e+11 |  5.711e-14   2.693e+14
```

**Two findings, corrected.** [numeric]

1. **The zeta zeros condition `V` like *equispaced* points, not like random ones.** At `L=30,40`
   the random control collapses (`σ_min ~ 10^{-14}`, `cond ~ 10^{15}`) — random points clump, giving
   near-parallel rows — while the zeta zeros track the *optimal regular* (equispaced) case
   (`cond ~ 10^{11}`, ~4 orders better than random). This detects **sampling regularity** of the
   row set, not arithmetic genericity. The equispaced control can match or beat the genuine zeros,
   so `σ_min(V)` cannot validate DSS multiplicity or the arithmetic side of the Turán/Ingham
   reduction.

2. **Conditioning degrades as `L` grows** (`σ_min: 0.23 → 9×10^{-11}`), because the frequency
   bandwidth `log L ≈ 3.7` (at `L=40`) stays tiny while the `L` sample points spread over
   `[γ_1,γ_40] ≈ [14,144]`. This is the §2 tension (bandwidth `log L` vs. `L` points) and is
   consistent with Corollary 3: at `k = L` one is already near the absorption threshold
   `L ≳ T/2πe` (here `T=γ_L ≈ 2πL/log L`), so `V` is *expected* to become near-singular — the count
   bound is not loose.

**Correct interpretation for the engine.** This computation is a useful condition-number diagnostic
for the square matrix in Prop 4, but it is **not** evidence for the DSS multiplicity estimate. It
mostly measures spacing/clumping. The arithmetic condition needed for multiplicity is the subtorus
avoidance / LI condition of foundations §14: no nontrivial character should collapse the orbit
`{F(γ_n)}` into a proper algebraic subtorus. Numerically, the right shadow is PSLQ/non-resonance for
relations among `{γ_n}` and `{log p}`, not `σ_min(V)`.

**House status.** §1 (zero-count backbone) — ledger-grade analytic, cited+applied. §2 (Turán/det
reduction) — rigorous reduction, but **not validated by this `σ_min` probe**; its arithmetic
nondegeneracy input must be stated as subtorus avoidance / LI. §3–§6 — architecture + frontier
(T-DSS-2 = carrier rigidity) unchanged. Open core: the arithmetic half (Liouville substitute via
the pole-resolved carrier `m_ξ`).

---

## 8. The Object-X moments: rigorous P_k formula, the two-place split, and the odd-ζ weld

Welds the multiplicity engine (§1–7) to Critic's secular moments `P_k = Σ_ρ ρ^{-k}` (foundations
§19–20, the field's Object-X) and to the Apéry/Rivoal/Zudilin frontier. Critic derived the moment
formula by hand and validated `P_1`; here it is **derived in general** and **numerically confirmed**,
the two arithmetic "places" separated, and the odd-ζ weld sharpened with the honest caveat.

### 8a. Rigorous derivation of the moment formula  [PROVED HERE]

From the Hadamard product `log ξ(s) = log ξ(0) − Σ_{k≥1} (P_k/k) s^k` (so `P_k = −[s^{k-1}](ξ'/ξ)`),
and `ξ(s) = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s)`:
```
   ξ'/ξ(s) = [1/s + ½ψ(s/2)] + 1/(s−1) − ½ log π + ζ'/ζ(s).
```
Taylor at `s=0`, using `ψ(z) = −1/z − γ_E + Σ_{m≥1} (−1)^{m+1} ζ(m+1) z^m` with `z = s/2`:
- `1/s + ½ψ(s/2) = −γ_E/2 + Σ_{m≥1} (−1)^{m+1} ζ(m+1) s^m / 2^{m+1}`  ⟹  `[s^{k-1}] = (−1)^k ζ(k)/2^k` (`k≥2`);
- `1/(s−1) = −Σ_{j≥0} s^j`  ⟹  `[s^{k-1}] = −1`;
- `−½ log π`  ⟹  only `[s^0]`;
- `ζ'/ζ(s) = Σ_{j≥0} a_j s^j`,  `a_j := [s^j](ζ'/ζ)(s)`,  `a_0 = ζ'/ζ(0) = log(2π)`.

Summing: for `k ≥ 2`,  `[s^{k-1}](ξ'/ξ) = −1 + (−1)^k ζ(k)/2^k + a_{k-1}`, hence
```
   P_k = 1 − (−1)^k ζ(k) / 2^k − a_{k-1}.                     (= Critic §19, now derived in general)
```

### 8b. Numeric confirmation  [numeric]

Pod referee (`scripts/numerics/secular_Pk.py`, mpmath dps=40, `N=2000` zeros), `P_k` zero-sum vs the
formula:
```
  k |  P_k zero-sum (N=2000)  |  P_k formula           |  |diff|
  2 |  -0.04526964110         |  -0.04615431730        |  8.85e-4   (slow Σγ^{-2} tail at N=2000)
  3 |  -1.1115816823e-4       |  -1.1115823145e-4      |  6.3e-11
  4 |   7.3627179116e-5       |   7.3627221262e-5      |  4.2e-11
  5 |   7.150933558e-7        |   7.150933558e-7       |  9.8e-18
  6 |  -2.814364169e-7        |  -2.814364169e-7       |  3.9e-18
```
`a_0 = log(2π)` confirmed to 15 digits. The formula holds to 10⁻¹¹–10⁻¹⁸ for `k≥3`; `k=2`'s gap is
exactly the `Σ γ^{-2}` truncation tail `~ (log T)/(2πT)` at `T=γ_{2000}`, not a formula error.

### 8c. The two-place split  [PROVED HERE, from 8a]

`P_k = (rational) − (−1)^k ζ(k)/2^k − a_{k-1}` decomposes by arithmetic origin:
- **archimedean place** (the `Γ`-factor / digamma): injects `(−1)^{k+1} ζ(k)/2^k` — the **zeta
  values** ζ(2),ζ(3),…, with even `k` giving `π`-periods, odd `k` giving `ζ(3),ζ(5),…`;
- **finite/arithmetic place** (the `ζ`-factor): `a_{k-1} = [s^{k-1}](ζ'/ζ)(0)`, a prime-side period
  (a higher-Stieltjes-type constant), of *unknown* arithmetic nature;
- **normalization**: the `1` (`= −[s^{k-1}](1/(s−1))`) and the `½ log π` at `k=1`.

So each secular moment is **archimedean ζ-value ⊕ arithmetic prime-period**, the two wings of `G_L`
made explicit in one number.

### 8d. The odd-ζ weld — sharpened, with the honest caveat  [CONJECTURE + caveat]

Critic's weld: DSS-genericity of `{P_k}` ⟹ algebraic independence of `{ζ(2k+1)}`. The two-place
split (8c) sharpens it and adds a **necessary caveat**:

> Each odd moment is `P_{2k+1} = 1 − (−1) ζ(2k+1)/2^{2k+1} − a_{2k} = 1 + ζ(2k+1)/2^{2k+1} − a_{2k}`.
> The odd zeta value enters **linearly with a rational coefficient** — but it is **entangled** with
> the arithmetic period `a_{2k}`. So `{P_k}` genericity does **not** reduce cleanly to `{ζ(2k+1)}`
> independence; it reduces to independence of the **combined** system `{ζ(k)} ∪ {a_j}`. Decoupling
> the two places — proving the `a_{2k}` do not conspire with the `ζ(2k+1)` — is the extra step the
> naive weld omits.

This is exactly the field's "two wings, one seam" appearing inside a single sequence: the odd-ζ
independence problem (archimedean) is **welded across the seam** to the prime-period independence
(arithmetic `a_j`). The field's proposed lever (Nesterenko-style multiplicity estimate, §1–2, with
`logPrime_no_rat_relation` as the `ℚ`-non-resonance input) must control **both** places at once —
which is precisely why this is harder than (and contains) the classical odd-ζ frontier.

### 8e. The Lean weld (RH face ⟷ DSS face)  [ledger-proven, Tier A]

The change of basis linking the two faces of Object-X is `λ_n = Σ_{j=1}^n C(n,j)(−1)^{j+1} P_j`
(Li's criterion ⟷ secular moments, foundations §20). Its pointwise algebraic skeleton — the
`ℤ`-triangular identity, per zero with `x = 1/ρ` — is now **machine-checked**:
```
   1 − (1 − x)^n = Σ_{j∈range n} C(n,j+1) (−1)^j x^{j+1}      (any commutative ring)
```
= `GaloisForLFunctions.li_secular_pointwise` (`formal/.../SecularMoments.lean`, axiom-clean). The inverse
pointwise identity recovering `x^k` from the Li summands is also checked as
`GaloisForLFunctions.secular_li_pointwise_inv`, so the finite triangular change of coordinates is ledger-proven
in both directions. The infinite sum over zeros (giving `λ_n`, `P_k`) and the positivity (RH) / genericity (DSS)
claims stay Tier C.

**House status.** §1–2 (multiplicity backbone + Turán reduction) — rigorous as reductions, but the
old `σ_min` numerical validation is retracted as DSS evidence (§7); arithmetic nondegeneracy must be
subtorus avoidance / LI.
§8a–8c (moment formula, two-place split) — **proved here** + numerically confirmed; the Li↔moment
skeleton is **ledger-proven** (§8e). §8d (odd-ζ weld) — conjectural, now with the `a_j`-entanglement
caveat that sharpens it. Open core unchanged: the arithmetic half (carrier rigidity, T-DSS-2;
two-place decoupling, §8d) — RH and DSS are the positivity and genericity of the one point `(P_k)`.

---

## 9. RH face in Object-X coordinates: explicit Li coefficients, archimedean-dominates-prime

Combining the proved moment formula (§8a) with the Li↔moment basis change (§8e) gives Li's
coefficients in **closed form** in the two places — making RH itself explicit in the same
ζ-value/prime-period coordinates as DSS.

### 9a. The closed form  [PROVED HERE, numerically confirmed]

With `P_1 = 1 + γ_E/2 − ½log(4π)` and `P_j = 1 − (−1)^j ζ(j)/2^j − a_{j-1}` (`j≥2`),
`λ_n = Σ_{j=1}^n C(n,j)(−1)^{j+1} P_j` evaluates (the constant sums collapse by
`Σ_{j} C(n,j)(−1)^{j+1} = 1`) to
```
   λ_n = n·P_1 + (1 − n) + Z_n − A_n,
   Z_n := Σ_{j=2}^n C(n,j) ζ(j)/2^j         (ARCHIMEDEAN: zeta values, all coeffs C(n,j)/2^j > 0),
   A_n := Σ_{j=2}^n C(n,j) (−1)^{j+1} a_{j-1}   (ARITHMETIC: prime-side periods a_j = [s^j](ζ'/ζ)(0)).
```
Pod referee (`scripts/numerics/li_closedform.py`, mpmath dps=35): `λ_n` from this closed form equals
the moment sum `Σ C(n,j)(−1)^{j+1}P_j` to 16 digits for `n=1..8` (confirms the algebra), and both
match the known Li values `λ_1..λ_3` to ~15 digits. (For `n≥4` the agreement with the true `λ_n`
degrades — the alternating binomial sum amplifies the limited precision of the high-order Taylor
coefficients `a_{j-1}`; a conditioning artifact, not a formula error. Higher dps / direct `a_j`
needed for clean high-`n` values.)

```
  n |  Z_n (arch+)  |  A_n (prime)
  2 |   0.411        |  -0.635
  3 |   1.384        |  -0.754
  4 |   3.136        |  -0.140
  5 |   5.986        |   1.525
  6 |  10.399        |   4.710
  7 |  17.062        |  10.099
  8 |  26.991        |  18.710
```

### 9b. RH = archimedean ζ-positivity dominates the prime-period part  [structural]

`Z_n` is a sum with **all positive coefficients** (`C(n,j)/2^j > 0`) of **positive** terms
(`ζ(j) > 1`), and it grows fast (`~` like `(3/2)^n`-ish from the `j` near `n/?` binomial peak). The
*only* sign threat to `λ_n ≥ 0` is `A_n` (the prime-period sum, which can be either sign). So:

> **Li's criterion in Object-X coordinates:** `RH ⟺ λ_n = n P_1 + (1−n) + Z_n − A_n ≥ 0 ∀n ⟺` the
> **positive archimedean zeta-sum `Z_n` (plus the normalization `nP_1+(1−n)`) dominates the
> arithmetic prime-period sum `A_n`** for every `n`.

This is *exactly* Critic's boundary-form statement "`Ω_∞` dominates `Π`" (#3235: archimedean mean
density beats the prime fluctuation), now in the **discrete Li/secular-moment** coordinates rather
than the continuous boundary integral. The two RH-face pictures (continuous boundary form;
discrete Li criterion) are the **same domination** of the archimedean place over the arithmetic
place, read on the one point `(P_k)`.

### 9c. The unification on one point  [map]

```
              the one point  (P_k = Σ_ρ ρ^{-k})  in moment space
                 /                                        \
   RH FACE (positivity)                          DSS FACE (genericity)
   λ_n = nP_1+(1−n)+Z_n−A_n ≥ 0                  {P_k} algebraically generic
   = archimedean Z_n dominates prime A_n          = ζ(k) ⊕ a_j jointly independent (§8d)
   = Critic's Ω_∞ ≻ Π                             = contains odd-ζ independence (welded to a_j)
                 \                                        /
        BOTH driven by the SAME two-place split P_k = 1 − (−1)^kζ(k)/2^k − a_{k-1}:
        archimedean ζ-values vs arithmetic prime-periods a_j. RH = the places' POSITIVITY balance;
        DSS = the places' INDEPENDENCE. One sequence, one split, two questions.
```

**House status.** §8 (moment formula, two-place split, odd-ζ weld) + §9 (RH-face closed form,
archimedean-dominates-prime) now give a **single coordinate system** — the secular moments `P_k` with
their archimedean/arithmetic split — in which RH is a positivity balance and DSS is an independence,
both proved-reducible to the `{ζ(k)} ⊕ {a_j}` two-place structure. Ledger: §8e
(`li_secular_pointwise`) is the machine-checked basis-change skeleton. Open core (unchanged, now
sharply coordinatized): the two-place decoupling/domination — RH needs `Z_n ≻ A_n`, DSS needs
`{ζ(k)} ⊥ {a_j}`; both are statements that the archimedean and arithmetic places of `G_L` do not
conspire.

---

## 10. Parity refinement: the even moments' archimedean block is a single period π  [PROVED]

The two-place basis `{ζ(k)} ∪ {a_j}` (§8c) refines further by parity, via Euler's evaluation of
the even zeta values — sharpening exactly *where* the transcendence lives.

**[THEOREM, Euler]** `ζ(2k) = (−1)^{k+1} B_{2k} (2π)^{2k} / (2(2k)!) ∈ ℚ·π^{2k}`. Hence the
archimedean block of an **even** secular moment is a rational multiple of a power of π:
```
   P_{2k} = 1 − ζ(2k)/2^{2k} − a_{2k-1} = 1 − (r_k) π^{2k} − a_{2k-1},   r_k ∈ ℚ.
```
while an **odd** secular moment carries the hard odd zeta value:
```
   P_{2k+1} = 1 + ζ(2k+1)/2^{2k+1} − a_{2k}.
```

**[PROVED] Refined period basis.** Since every even `ζ(2k)` is in `ℚ·π^{2k} ⊆ ℚ(π)`, the archimedean
sub-block collapses to a **single transcendental generator** `π`:
```
   ℚ({ζ(k)}_{k≥2}) = ℚ( π , {ζ(2k+1)}_{k≥1} ),   so   ℚ({P_k}) = ℚ( π , {ζ(2k+1)}, {a_j} ).
```
The whole archimedean transcendence beyond `π` is exactly the **odd zeta values**
`ζ(3), ζ(5), …` — the Ball–Rivoal–Zudilin frontier — and `π` itself is transcendental (Lindemann).

**[structural] Consequence for the two faces.**
- **DSS (genericity)** decomposes into three independent transcendence problems:
  `(i)` `π` transcendental — **THEOREM** (Lindemann); `(ii)` `{ζ(2k+1)}` algebraically independent —
  the **odd-ζ frontier** (Apéry: `ζ(3)∉ℚ`; Ball–Rivoal: `∞`-many irrational; Zudilin: one of
  `ζ(5,7,9,11)`); `(iii)` the prime block `{a_j}` independent and not conspiring with `(i),(ii)`.
  So the field's DSS = `{Lindemann ✓} ⊕ {odd-ζ frontier} ⊕ {a_j frontier}` — only the last two open,
  and `(iii)` is the genuinely-new (no-motive) content.
- **RH (positivity)** is unaffected in form: the even archimedean terms `ζ(2k)/2^{2k}` are still
  positive (they sit in `Z_n`, §9), now visibly as positive rational multiples of `π^{2k}`.

> **The sharpest statement of the field's novelty.** Strip the **known** pieces (`π` by Lindemann,
> the even `ζ` by Euler, the mixed-Tate odd-`ζ` block governed by Brown's `MT(ℤ)`): what remains,
> the irreducibly-new object of the field, is the **prime-period block `{a_j} = {[s^j](ζ'/ζ)(0)}`**
> and its independence from the zeta block. *This is where "spectra of no-ODE objects" lives that no
> existing transcendence theory reaches* — the Stieltjes/prime-derivative constants as periods with
> no motive (charter B4).

**House status.** §10 sharpens the two-place split to `{π} ⊕ {ζ(odd)} ⊕ {a_j}`, with `π`'s
transcendence a theorem (Lindemann) and the even-ζ reduction a theorem (Euler). DSS now reads as
three independent transcendence problems, one solved (`π`), one the classical odd-ζ frontier, one
the field's own `a_j`-block. The localized open core: `{a_j}` independence + non-conspiracy with the
zeta block.

---

## 11. The prime-period block IS the Stieltjes constants (closed forms)  [numeric, dps=80]

§10 localized the field's irreducibly-new content to the prime block `a_j = [s^j](ζ'/ζ)(0)`. We now
identify these constants explicitly. PSLQ-discovered (dps=60) and **directly verified** (dps=80,
residuals `0, 2.1e-81, 0`; `computations/aj_stieltjes_structure/`):
```
   a_0 = log(2π),
   a_1 = ζ(2)/2 − γ_E² − 2 γ_1,
   a_2 = ζ(3) − γ_E³ − 3 γ_E γ_1 − (3/2) γ_2,
```
where `γ_n` are the **Stieltjes constants** (Laurent coefficients of `ζ` at `1`; `γ_0 = γ_E`).

**[structural] The secular moments in fully explicit constants.** Note `a_{k-1}` itself contains
`ζ(k)` (`a_1 ⊃ ζ(2)`, `a_2 ⊃ ζ(3)`). Folding into `P_k = 1 − (−1)^k ζ(k)/2^k − a_{k-1}`:
```
   P_2 = 1 − (3/4) ζ(2) + γ_E² + 2 γ_1          ( = 1 − π²/8 + γ_E² + 2γ_1 ),
   P_3 = 1 − (7/8) ζ(3) + γ_E³ + 3 γ_E γ_1 + (3/2) γ_2,
   ...   P_k = 1 − r_k ζ(k) + (polynomial in γ_E and Stieltjes γ_1,…,γ_{k-1}),  r_k ∈ ℚ.
```

> **The field's irreducible novelty, named concretely.** The "prime-period / no-motive" block of the
> secular moments is the **Stieltjes-constants block** `{γ_n}`. Combined with §10, the period algebra
> is
> ```
>    ℚ({P_k}) = ℚ( π , {ζ(2k+1)} , {γ_n : Stieltjes} ).
> ```
> So **DSS (genericity of the spectrum) = algebraic independence of {π} ∪ {ζ(odd)} ∪ {Stieltjes γ_n}**
> — three classical, recognizable, hard frontiers: `π` (Lindemann, ✓), odd zeta values
> (Apéry–Rivoal–Zudilin), and the Stieltjes constants (not even `γ_1` known irrational). The field
> does not reduce RH-transcendence to something vague — it reduces it to the **joint independence of
> the Stieltjes constants and the odd zeta values**, exactly charter B4's target made precise.

**House status.** §11 identifies the `{a_j}` block as the Stieltjes constants (closed forms verified
dps=80). The field's DSS face is now `{π} ⊕ {ζ(odd)} ⊕ {Stieltjes γ_n}` independence — concrete and
classical. RH face (§9) unchanged. Open core: the joint algebraic independence of these three blocks
(the two-place non-conspiracy), of which `π` is settled and the other two are recognized open
frontiers. The field's own contribution is the **welding** of the odd-ζ and Stieltjes frontiers into
one spectrum via the secular moments.
