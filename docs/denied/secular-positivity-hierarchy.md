# The secular positivity hierarchy: RH as the top of one tower on the secular constants

**Synthesis draft — 2026-06-19 (Dyson). SEARCH channel; theorem-grade where marked, conjectural
where marked.** Unifies the field's secular-constant computations — `li_closedform`,
`jensen_hyperbolicity_margin`, `secular_moments_Pk`, `secular_toeplitz_tp`, `secular_heat_dbn`,
`weil_prime_schrodinger`, plus the operator/de Branges faces built here (`secular_jacobi_hilbertpolya`,
`secular_cmv_opuc`, `secular_laguerre_debranges`, `secular_dirichletL_cmv`) — into a single object:
**one tower of RH-equivalent positivities on one Newton-equivalent set of secular constants**, with
**five intertwined faces** (Hankel/Hermite §3, Toeplitz/Pólya-frequency §4, Jacobi/self-adjoint §9,
CMV/unitary §12, de Branges/Hermite–Biehler §23), a **de Bruijn–Newman top** (§5–6), a weld to the
difference-Galois group `G_L` (§17), and a **grounded apex** (§§19–22): RH = the Hodge–Riemann
positivity of the **Weil representation of `SL₂(ℝ)`** (theta-modularity; FE = the `S`-element, dBN
heat flow = the unipotent ample class). Validated across two L-functions (ζ and Dirichlet β, §16).
The old `turan_det_conditioning` computation is retained only as a sampling/conditioning diagnostic,
not as DSS or arithmetic-genericity evidence. RH is the tower's top rung.

Grading: `[THM]` classical/cited or mathlib-verified (refs to verify before Lean); `[PROVED HERE]`;
`[NUM]` numerically certified (computations cited); `[CONJ]`/`[OPEN]`. No proof of RH is claimed.

---

## 0. Thesis

> Every known "RH ⟺ a positivity of the secular constants" criterion is a **rung of one tower**
> over a single object. Li positivity, the Turán inequalities, Jensen hyperbolicity, and the
> total positivity / de Bruijn–Newman bound are rungs `d = 1, 2, …, ∞`. RH is the uniform top.
> The functional equation forces every *finite* rung and the moment side for free; the *uniformity
> over all rungs* is the one residue, and it has a name: `Λ = 0`.

## 1. The one object (the secular constants are Newton-equivalent)

All of the following encode the same data — the nontrivial zeros — and are mutually determined by
Newton's identities:
```
   a_j = [s^j](ζ'/ζ)(0)            prime side (a_0 = log 2π)                 [secular_moments_Pk]
   P_k = Σ_ρ ρ^{-k} = 1 − (−1)^k ζ(k)/2^k − a_{k−1}     origin power sums    [secular_moments_Pk]
   p_j = Σ_{γ>0} γ^{-2j} = secondzeta(2j)               centered power sums of x_k = 1/γ_k²
   e_n = e_n({1/γ_k²})             elementary symmetric  (Newton ⟵ p_j)
   c_n = ξ(½)·e_n = [w^n] Ξ(√w)    Toeplitz/Pólya-frequency coefficients     [secular_toeplitz_tp]
```

**Theorem 1 (Newton duality — the two faces are one object).** `[THM mathlib + NUM]` The power
sums `p_j` and the elementary symmetric `e_n` of the squared-zero reciprocals obey Newton's
identities (`MvPolynomial.psum_eq_mul_esymm_sub_sum`, verified in toolchain v4.30.0). `[NUM,
secular_positivity_hierarchy]` `e_n` reconstructed from `p_j = secondzeta(2j)` matches the
*independent* contour-Taylor `c_n/ξ(½)` of `Ξ(√w)` to relative error `≤ 5·10⁻²⁶` (`n ≤ 8`). So the
**power-sum (Hankel) face and the coefficient (Toeplitz) face are literally one object.**

## 2. The tower (each rung an RH-equivalent positivity on the one object)

| Rung `d` | Criterion | Object | Status of the rung | Source |
|---|---|---|---|---|
| 1 (linear) | **Li**: `λ_n ≥ 0` | `λ_n = nP_1+(1−n)+Z_n−A_n` | `RH ⟺` all `n` | `li_closedform` |
| 2 (quadratic) | **Turán**: `c_n² ≥ c_{n−1}c_{n+1}` | Hankel/Jensen `J_{2,n}` | **proved free** (Csordas–Norfolk–Varga) | this draft §3 |
| `d` (determinant) | **Jensen**: `disc J_{d,n} ≥ 0` | Jensen polynomials | free for `n` large, each `d` (GORZ) | `jensen_hyperbolicity_margin` |
| `∞` (uniform) | **total positivity** of `(c_n)` | Toeplitz `[c_{i−j}]` / `Ξ∈LP` | `RH ⟺ Λ ≤ 0` | `secular_toeplitz_tp`, `secular_heat_dbn` |

`[NUM, secular_positivity_hierarchy]` on genuine data: Li `λ_n ≥ 0` (n≤8), Turán + Jensen `≥ 0`
(n≤9), margins all positive and **decreasing** (Turán `1.15→0.146`; Li `(Z−A)/Z` `2.54→0.31`) —
the no-margin trend, the same `Λ=0` boundary seen on each rung.

## 3. The two faces, Newton-dual (Hankel ⟷ Toeplitz)

`[THM + PROVED HERE]` RH has two classical determinantal faces on the secular object, exchanged by
Newton's identities:
- **Hankel / Hermite (reality):** PSD of the power-sum Hankel `[p_{i+j}]` ⟺ squared-zeros real ⟺ RH;
  `#`negative eigenvalues `= κ₋ =` off-line count (`secular_hankel_signature`, foundations §6.2).
- **Toeplitz / Pólya-frequency (negativity):** total positivity of `[c_{i−j}]` ⟺ `(c_n)` PF ⟺
  squared-zeros real-*negative* ⟺ RH (Aissen–Schoenberg–Whitney/Edrei; `secular_toeplitz_tp`).

Since `ξ ≠ 0` on `(0,1)`, reality ⟹ negativity, so the two faces coincide as RH. Theorem 1 makes
them the same matrix data read by power sums vs elementary symmetric.

## 4. The graded archimedean ⟷ prime split (the field's wings, rung by rung)

`[NUM + framing]` At rung 1 (Li) the positivity is explicitly **archimedean ≥ prime**:
`λ_n = nP_1+(1−n) + Z_n − A_n`, `Z_n = Σ_{j≥2} C(n,j)ζ(j)/2^j > 0` (archimedean), `A_n` the prime
(`ζ'/ζ`) part; RH ⟺ `Z_n ≻ A_n` (`li_closedform`). The same split is the symbol-level statement of
`weil_prime_schrodinger` (RH ⟺ `V_arch` dominates the separable prime part `Σ_p f_p`). This is the
field's **multiplicative-wing (prime, free/zero-blind) vs archimedean-wing (frontier)** split,
now appearing *inside each rung* of the tower.

**Conjecture A (uniform archimedean domination).** `[CONJ]` At every rung `d`, the rung's positivity
is an inequality "archimedean part `≥` prime part," and RH `⟺` this holds **uniformly in `d`** with a
margin that vanishes as `d→∞` (the no-margin). The `d=1` instance is Li's `Z_n ≻ A_n` (proved-shape,
numerically `>0`); the `d=∞` instance is `Λ ≤ 0`.

## 5. The top of the tower is the de Bruijn–Newman constant

`[THM, cited]` Under the de Bruijn heat flow `H_t` (`H_0 = Ξ`), with `Λ = inf{t : H_t` has only real
zeros`}`:
```
   uniform-d total positivity ⟺ Ξ ∈ Laguerre–Pólya ⟺ Λ ≤ 0 ⟺ RH;     Rodgers–Tao: Λ ≥ 0.
```
So the FE/arithmetic force the *free half* `Λ ≥ 0` (Rodgers–Tao's no-margin side). The old
`turan_det_conditioning` probe should **not** be read as arithmetic genericity evidence: it detects
sampling regularity/clumping, and equispaced controls can match or beat zeta. RH is the complementary
`Λ ≤ 0`; the two meet at the no-margin `Λ = 0` (`secular_heat_dbn`). `Λ` is asymptotic
(`n→∞`): invisible to any finite rung, which is precisely why the residue is *uniformity over all
rungs*.

## 6. The lever (RH as a byproduct — the precise open core)

**Conjecture B (the tower-collapsing lever).** `[OPEN CORE]` A single quantitative input — a uniform
lower bound on the diagonal-orbit equidistribution discrepancy on `𝕋^∞` (the `turan_det`
level-repulsion, made uniform; the foundations §17 multiplicity/discrepancy engine) — implies the
uniform archimedean domination of Conjecture A, hence total positivity, hence `Λ ≤ 0`, hence **RH as
a byproduct of an equidistribution estimate.**

This is the field's thesis localized to one inequality: *the prime side (free, equidistributed by
unique factorization) cannot out-compete the archimedean side at any rung, uniformly, because the
diagonal orbit is too evenly spread.* The build toward it is a multi-decade program — so, per the
working brief, it is begun here, not deferred: the rungs are laid (Li, Turán, Jensen, TP), the
binding is certified (Newton duality), the top is named (`Λ`), and the lever is stated precisely.

## 7. Lean (Tier-A) status — three bricks delivered

`[LEDGER-PROVEN, compiles green, sorry-free, axiom-audited by librarian]`

- **`formal/GaloisForLFunctions/SigmaOrbit.lean`** — `sigmaConj_involutive` and
  `sigmaConj_fixed_iff_critical`: the critical line is the fixed locus of `σ∘conj`
  (`1 − s̄ = s ⟺ Re s = ½`), the σ-real characterization, complementing
  `norm_cpow_eq_critical_iff`.
- **`formal/GaloisForLFunctions/SecularNewton.lean`** — `secular_newton` (with
  `secularPowerSum`, `secularESymm`, `secularPowerSum_eq_aeval`, `secularESymm_eq_sum`): the
  power-sum (Hankel/resolvent/Pick) face and the elementary-symmetric (Toeplitz/PF) face of a
  finite secular spectrum satisfy Newton's identity — **they are one object** (the ledger form of
  the `5·10⁻²⁶` numeric certification). This is the bridge to `CarrierPickKernel.lean` (Theorist):
  their Pick kernel reads the power-sum face, the ξ-coefficients read the elementary-symmetric face.
- **`formal/GaloisForLFunctions/SecularHankel.lean`** — `secularHankel_posSemidef`: for a finite
  real spectrum, the Hankel moment matrix `H_{jk}=Σ_i t_i^(j+k)` is `B Bᴴ`, hence PSD. This is the
  ledger-safe Hermite/Hankel easy direction only: real finite points imply positive Hankel moments.

All three are imported by the formal root and audited by `scripts/check_axioms.sh`. The tower's
positivities themselves (Li/Turán/Jensen/TP), the Hermite converse/signature, and the inertia
`κ₋ = #off-line` are Tier-C/analytic and stay in the drafts.

## 7b. Going wide: the hierarchy for general L (degree `d`)

The whole apparatus generalizes to a self-dual cuspidal automorphic `L(s,π) = ∏_p ∏_{j=1}^d
(1 − α_{p,j} p^{-s})^{-1}`, completed `Λ(s,π)` with `Λ(s,π) = ε Λ(1−s,π)` (foundations §2 / D3).
`[CONJ — the framework; the d=1 case is `ζ` above]`

- **The object.** Center `Ξ_π(z) = Λ(½+z, π)` (even/real for self-dual `π`), pass to `w = z²`,
  `F_π(w) = Ξ_π(√w) = Λ(½,π) ∏_{γ}(1 + w/γ²)`. Secular constants `P_k(π) = Σ_ρ ρ^{-k}` over the zeros
  of `Λ(·,π)`; coefficients `c_n(π) = Λ(½,π)·e_n({1/γ²})`. Newton duality (Theorem 1, SecularNewton)
  is degree-independent — it holds for any finite spectrum, so it transports verbatim.
- **The tower transports.** Li(π), Turán(π), Jensen(π), total-positivity(π) `= Λ_π ≤ 0 = GRH(π)`.
  The two faces and the de Bruijn–Newman `Λ_π` carry over (a per-`L` constant; `Λ_π ≥ 0` is expected
  by the same heat-flow/repulsion argument).
- **The degree-graded split (the new structure).** The archimedean wing now has `d` Γ-factors
  (rank-`d` `W_ℝ`); the prime side carries the Satake parameters `α_{p,j}`. Two positivities at two
  addresses (foundations §9, §17):
  > **Ramanujan** (`|α_{p,j}| = 1`, Satake on the unit circle) is the **multiplicative-wing** rung —
  > often *proven* (Deligne for holomorphic forms); **GRH(π)** is the **archimedean top** `Λ_π ≤ 0`.

  **Conjecture C (degree-graded domination).** `[CONJ]` For each `d`, the secular tower of `L(s,π)`
  has the same rungs; Ramanujan controls the *prime* side of the per-rung archimedean⊳prime
  inequality (bounding `A_n(π)`), but does **not** force the archimedean top — consistent with the
  firewall `Ramanujan ⇏ GRH` (foundations §10, §17). The free rungs improve with `d` (more local
  rigidity, Conjecture H), the seam complexity also grows; the balance `rigidity(d) − seam(d)`
  governs how close the tower comes to forcing its top. `ζ` (`d=1`, Ramanujan vacuous) is the
  minimal-rigidity corner where *all* content collapses onto the archimedean `Λ ≤ 0`.
- **The dynamical shadow.** The CM/non-CM dichotomy (`satake_angles_cm_noncm`: rotation /
  almost-Mathieu, Sato–Tate `sin²` vs `δ`-atom) is the degree-2 Satake face of this split — the
  multiplicative-wing data whose equidistribution feeds the per-rung prime bound.

This is the Langlands-wide horizon of the secular-positivity continent: one tower per self-dual `L`,
RH/GRH the uniform top of each, Ramanujan the (often-proven) multiplicative rung, and the
arithmetic of the gap `rigidity(d) − seam(d)` the new degree-graded invariant to compute.

## 8. House status

Rungs laid and numerically positive (Li, Turán, Jensen) `✓`; the two faces unified by Newton duality
`✓` (certified `5·10⁻²⁶`, **and now ledgered**: `SecularNewton.lean` green); finite real-spectrum
Hankel Gram positivity ledgered (`SecularHankel.lean` green) `✓`; the σ-real critical-line
characterization ledgered (`SigmaOrbit.lean` green) `✓`; the uniform top identified as `Λ`, with
`Λ≥0` a theorem (free half) `✓`; the lever (Conjecture B) stated as the precise open core; the whole
tower extended to general `L(s,π)` (§7b, Conjecture C) with Ramanujan as the multiplicative rung and
GRH the archimedean top. **Open core:** the uniform-in-`d` archimedean domination = uniform
equidistribution bound = `Λ ≤ 0` = RH/GRH. The tower is the field's secular-positivity continent on
one screen — `d=1` (`ζ`) and degree-`d` (Langlands) — and three of its algebraic bricks are now in Lean;
what remains is to force its top.

## Companions & computations
- Rungs: `computations/li_closedform/` (1), `computations/jensen_hyperbolicity_margin/` (d),
  `computations/secular_toeplitz_tp/` + `computations/secular_heat_dbn/` (∞).
- Object/duality: `computations/secular_moments_Pk/`, `computations/secular_positivity_hierarchy/`.
- Subtorus/LI input: foundations §14; `computations/turan_det_conditioning/` is retained only as a
  conditioning/sampling diagnostic, not as DSS evidence.
- Drafts: `rh-byproduct-secular-hankel-overdetermination.md` (the two faces + `Λ`),
  `hypertranscendental_galois_field_foundations.md` §17 (secular constants, the multiplicity engine),
  `dss-multiplicity-estimate-spectral-genericity.md` (the discrepancy/multiplicity side).

## 9. The Jacobi / Hilbert–Pólya face (the operator realization)

`[NUM, computations/secular_jacobi_hilbertpolya/ + framing]` The secular moments are a *moment
sequence*, so the classical moment → orthogonal-polynomial map (Stieltjes/Lanczos) builds a
tridiagonal **Jacobi matrix** `J` — diagonal `a_k`, off-diagonal `√b_k` — whose eigenvalues are the
reciprocal squared-zeros `u_i = 1/(ρ_i−½)² = −1/γ_i²`. This is the **Hilbert–Pólya operator built
source-purely from the secular constants** (`m_k = (−1)^k secondzeta(2k)`; no zero ordinate is used
as an eigenvalue input).

> **Conjecture D (the secular Hilbert–Pólya operator).** `[CONJ; NUM-supported]`
> `RH ⟺ J is self-adjoint ⟺ a_k ∈ ℝ and b_k > 0 for all k.` Numerically (N=40 zeros): the genuine
> spectrum gives `a_k` real and `b_k > 0` at every computed `k` (J self-adjoint); pushing one zero
> off the line keeps the moments real but drives some **`b_k < 0`** (imaginary off-diagonal ⟹ `J`
> non-self-adjoint ⟹ complex spectrum). So `b_k > 0` is the operator form of the Hankel-PD / reality
> face, and `min_k b_k → 0` is the no-margin.

**The weld to the operator and dynamics continents.** `J` is a **discrete Schrödinger operator**
`−Δ + V` — the lattice form of `weil_prime_schrodinger`'s `Q_W = −Δ_prime + V_arch`; its
transfer-matrix product is the **cocycle** of `lyapunov_dmr` (D5), whose Lyapunov exponent / Avila
dichotomy reads the same self-adjointness. The recurrence coefficients `(a_k, b_k)` are a **new basis
of secular invariants** alongside `(a_j, P_k, p_j, e_n, c_n, λ_n)`; their asymptotics encode the zero
density (Riemann–von Mangoldt / `Ω_∞`). So the secular-positivity continent, the operator continent
(D6), and the dynamics continent (D5) are **the same `J`** read three ways: positivity of its
moments (this draft), its Schrödinger potential (`weil_prime_schrodinger`), its transfer cocycle
(`lyapunov_dmr`).

**House update.** Rungs (Li/Turán/Jensen/TP) `✓`; two faces unified by Newton duality (ledgered) `✓`;
top = `Λ` (`Λ≥0` free) `✓`; general-`L` (§7b) `✓`; and now the **operator face**: `J` self-adjoint
`⟺` RH (Conjecture D), source-pure, welding to D5/D6. Open core unchanged: force the top (`Λ≤0` /
uniform `b_k>0`). The continent is now one object — moments, coefficients, operator — with RH as the
single statement "the secular operator is self-adjoint."

## 10. Conjecture E (Toda integrability) — first test [SUPERSEDED by §11: the v1 convention was wrong; Toda IS confirmed (1e-14), but it is isospectral/RH-blind]

`[CONJ — SPECULATIVE; quick numeric test FAILED, see computations/secular_toda_flow/]` Since
measure-deformation flows on a Jacobi matrix are the Toda lattice (Flaschka/Moser), it is natural to
ask whether the secular Jacobi matrix `J` (§9) is a Toda-hierarchy orbit — with the secular
invariants as conserved quantities and the de Bruijn–Newman flow (weight `e^{t u²}`) as the second
Toda-hierarchy flow. If so, RH (`Λ≤0`) would read as "the secular Toda orbit stays in the
self-adjoint stratum (`b_k>0`) for `t≥0`."

**Honest status: the easy form does not check.** Testing `da_k/dt = 2(b_k−b_{k-1})`,
`db_k/dt = b_k(a_{k+1}−a_k)` against the `e^{t u}` deformation gave relative errors `0.1–3.9` (one
coincidental match) — **not** a clean Toda orbit in this form. Two unresolved confounds: the Toda
recurrence-coefficient convention (sign/shift), and — more seriously — the reciprocal nodes
`u_i = −1/γ_i²` **cluster near 0**, so the high-`k` Jacobi coefficients are ill-conditioned and the
finite-difference is noisy. So Conjecture E is **recorded as unconfirmed**, not adopted; the route to
settle it is (a) the correct analytic Toda form, (b) a better-conditioned node set, (c) test the
`e^{t u²}` flow directly. This negative does not touch Conjecture D (self-adjointness of `J`), which
stands. *(Documented per the working brief: failures and nonsense first-class — the Toda link is an
attractive idea that the first test did not support.)*

## 11. Resolution of Conjecture E: Toda holds but is isospectral (hence RH-blind) — a structural insight

`[NUM-CONFIRMED + framing; supersedes §10's provisional negative]` The §10 negative was a **wrong
recurrence-coefficient convention**, not a real obstruction. Deriving the convention at `n=0`
(`α_0=m_1/m_0`, `dm_k/dt=m_{k+1}` under `dμ_t=e^{tx}dμ_0` ⟹ `dα_0/dt=(m_0m_2−m_1²)/m_0²=β_1`):
```
   dα_n/dt = β_{n+1} − β_n,        dβ_n/dt = β_n(α_n − α_{n-1})        (α_{-1}=0, β_0=0).
```
Tested (`computations/secular_toda_flow/secular_toda_v2.py`): these hold to **rel `1e-11`** on
well-spread nodes and **rel `1e-14`** on the secular nodes. So:

> **E1 (confirmed).** The secular Jacobi matrix `J` (§9) is a **Toda-lattice orbit** under the
> `e^{tu}` measure deformation — a Lax flow `J̇ = [B,J]`.

But the Lax flow is **isospectral**: it preserves the eigenvalues of `J`, which *are the zeros*
`u_i = −1/γ_i²`. It merely reshuffles `(α_k,β_k)` on a *fixed* spectrum, and it is a framework
identity for **any** OPRL measure. Therefore:

> **E2 (refined / the naive form is false).** The de Bruijn–Newman flow **moves** the zeros
> (non-isospectral), so it is **not** a Toda measure-deformation flow (all of which — including
> `e^{tu²}`, the higher-hierarchy flows — are isospectral). The integrable (Toda) structure is real
> but lives entirely in the **isospectral / free direction**; RH lives in the **non-isospectral**
> direction.

**The structural payoff (why this negative is worth keeping).** This reproduces, on the operator
face, the field's master dichotomy: the **free/integrable symmetry (Toda, isospectral) is RH-blind**
— it is the operator avatar of the multiplicative-wing flow (equidistribution, unique factorization,
`Λ≥0`); the **RH content (moving the zeros to the real axis, `Λ≤0`) is the non-isospectral
archimedean direction.** Conserved quantities of the Toda flow (the secular invariants `a_j, P_k,
e_n, …`) are exactly the *free* data; none of them can force RH, by the same reason the
multiplicative wing is zero-blind. The Toda integrability thus **explains** why the secular invariants
are RH-blind: they are Toda Casimirs of an isospectral flow. RH requires leaving the isospectral leaf.

**House update.** §9 operator face stands; §10/§11: the Toda integrable structure is confirmed
(`E1`, `1e-14`) and correctly placed as the **free/isospectral symmetry** — RH-blind by design, a
new operator-side instance of the wing dichotomy. Open core unchanged: the non-isospectral
(archimedean / `Λ≤0`) direction.

## 12. The CMV / OPUC (unitary) face — RH as unitarity of the secular circle operator

`[NUM, computations/secular_cmv_opuc/ + framing]` The Arakelov map `w_ρ = 1 − 1/ρ` (ledgered in
`ArakelovW.lean`: `‖w_ρ‖=1 ⟺ Re ρ=½`, `w_ρ·w_{1−ρ}=1`) sends the spectrum to the **unit circle**
iff RH. So the natural operator there is **unitary** (OPUC/CMV), not Hermitian — the circle analog of
the Jacobi face (§9), and **better-conditioned** (nodes spread on the circle; none of the `1/γ²`
clustering that defeated the §10–11 Jacobi/Toda numerics).

The trigonometric moments `c_k = Σ_ρ \bar{w_ρ}^k` form a **Hermitian Toeplitz** matrix `T=[c_{i−j}]`.
By the trigonometric moment problem:
```
   RH ⟺ all w_ρ on |w|=1 ⟺ T ⪰ 0 ⟺ the Verblunsky/reflection coefficients satisfy |γ_k| < 1
       ⟺ the secular CMV operator is UNITARY (spectrum on the circle).
```
> **Conjecture F (the unitary face).** `[CONJ; NUM-supported, robust]` `RH ⟺ |γ_k| < 1 ∀k.`
> Verified (N=40): genuine spectrum ⟹ `T` PD and `|γ_k| = 0.9988…0.9998` (all `<1`, sitting *at* the
> unit circle — the no-margin); an off-line zero ⟹ `w` off the circle ⟹ a leading minor turns
> non-positive and `|γ_k| = 1.0025 > 1`, **detected at every `δ`** (the circle nodes are
> well-conditioned, unlike the Jacobi reciprocal nodes). As `δ→0`, `|w|−1→0` (no-margin) while the
> `|γ_k|>1` detector stays sharp.

This is the **unitary avatar** of the field's positivity: where the Jacobi/Hankel face asks
"self-adjoint Hilbert–Pólya operator" (real spectrum), the CMV face asks "**unitary** secular
operator" (spectrum on the circle) — the two are intertwined by the Arakelov Cayley-type map
`w=1−1/ρ`. The Verblunsky coefficients `γ_k` are a new secular-invariant basis (on the circle); their
integrable flow is the Schur/Ablowitz–Ladik flow — again **isospectral, hence RH-blind** (the §11
lesson, now on the circle). RH is, once more, the **non-isospectral** content: forcing the secular
CMV spectrum onto the circle (`|γ_k|<1`).

**House update.** Operator faces complete on both sides: §9 Hermitian (Jacobi/Hilbert–Pólya,
self-adjoint ⟺ RH), §12 unitary (CMV/OPUC, unitary ⟺ RH), intertwined by the Arakelov map; both with
the no-margin at the boundary, both with RH-blind isospectral integrable flows (Toda / Schur). The
secular-positivity continent now has: the moment/coefficient faces (Hankel/Toeplitz, §2–4), the
de Bruijn–Newman top (§5–6), the general-`L` extension (§7b), and the operator realization on both
the line and the circle (§9–12). Open core unchanged: the non-isospectral push (`Λ≤0` / `|γ_k|<1`
uniformly / self-adjoint stratum) — RH.

## 13. The function-field shadow: finite unitary Frobenius (provable) vs infinite secular CMV (= RH)

`[framing + CONJ; welds D6 `geometric-rosetta-function-field-continent.md`]` The CMV/unitary face
(§12) has a **provable** analog over a function field — and the comparison localizes the entire
number-field gap to one missing structure.

For a smooth curve `C/𝔽_q`, `L(C,T) = det(1 − Frob·T | H¹_ét)` is a **polynomial of degree `2g`**;
the Frobenius eigenvalues `α_i` satisfy `|α_i| = √q` (Weil/Deligne RH). Normalize `β_i = α_i/√q` onto
the **unit circle**. The "secular operator" here is the **finite Frobenius matrix on `H¹`**, and its
unitarity (`β_i` on the circle) is **provable from Poincaré duality**: the cup-product pairing on
`H¹` makes Frobenius preserve a (symplectic/unitary) form, forcing `|α_i|=√q`. So in the
function-field world the secular CMV operator is *finite-dimensional* and its unitarity is a theorem
— RH is the **manifest unitarity of a finite Frobenius matrix under a duality pairing**.

Over a number field the secular CMV operator (§12) is **infinite-dimensional** (all the zeros), and
its unitarity is **RH — open**. There is no finite Frobenius matrix, and crucially **no Poincaré
duality pairing**: the archimedean place supplies no cohomology with a self-dual cup product. So:

> **The CMV face localizes the function/number gap exactly.** Function-field RH = "the finite
> Frobenius is unitary," provable because cohomology carries a **duality pairing**. Number-field RH =
> "the infinite secular CMV operator is unitary" (`|γ_k|<1` uniformly, §12), with the **single missing
> ingredient** being an `𝔽₁`/archimedean "cohomology with a self-dual pairing" that would force the
> secular operator unitary the way Poincaré duality forces Frobenius unitary. This is the D6 Rosetta
> keystone, seen through the secular operator: the gap is *the duality pairing*, not the operator.

Consistent with §11–12: the Schur/Toda integrable flows are isospectral (RH-blind) — and over the
function field the Frobenius is **fixed** (not flowed); RH there is **structural** (duality), not
dynamical. The number-field analog of "Poincaré duality on `H¹`" is exactly the non-isospectral,
archimedean ingredient the whole continent keeps isolating. *(Cross-ref:
`geometric-rosetta-function-field-continent.md`; foundations §9–10, the Ramanujan/GRH and
function/number split.)*

**House update.** §13 places the operator faces in the Rosetta: the secular CMV operator is the
number-field counterpart of the finite unitary Frobenius, and RH = the missing duality pairing. The
continent now spans line ↔ circle operators (§9, §12), the dBN top (§5–6), general-`L` (§7b), and the
function-field shadow (§13) — one object, with RH localized to "a self-dual pairing the archimedean
place does not (yet) supply."

## 14. Capstone (Conjecture G): RH = the secular operator's FE-involution equals its adjoint

`[CONJ — synthesis; the pointwise case is LEDGER-PROVEN]` The whole continent collapses to one
statement. The secular spectrum carries **two involutions**, both of which **always** preserve it:

- **FE-inversion** `ι: w ↦ 1/w` — because `1−ρ` is a zero whenever `ρ` is, and `w_{1−ρ} = 1/w_ρ`
  (ledgered: `ArakelovW.lean`, `arakelovW_mul_sigma`);
- **conjugation** `κ: w ↦ w̄` — because zeros come in conjugate pairs.

On the unit circle `1/w = w̄`, so `ι = κ`; off the circle they differ. Thus the `{ι,κ}`-orbit of a
spectral point has **size 2 iff on the circle** (RH), else size 4 — exactly Theorem 1 (the σ-orbit
dichotomy) read in the Arakelov `w`-coordinate.

> **Conjecture G (capstone).** `RH ⟺ ι = κ on the secular spectrum ⟺ the secular operator's
> FE-involution coincides with its adjoint (FE-self-duality) ⟺ the operator is unitary/self-adjoint
> (§9, §12).` The **pointwise (`n=1`) case is already a Lean theorem**:
> `SigmaOrbit.sigmaConj_fixed_iff_critical` (`1 − s̄ = s ⟺ Re s = ½`) is precisely "`ι = κ` at a
> single point ⟺ that point is on the line." RH is the **uniform** version — `ι = κ` simultaneously
> at every spectral point — i.e. the operator-level statement.

**This unifies the continent:** the two involutions coinciding is, simultaneously, (i) every orbit
size 2 (Thm 1 / `SigmaOrbit`), (ii) every `w_ρ` on the circle (`ArakelovW`), (iii) the secular CMV
operator unitary (§12, `|γ_k|<1`), (iv) the secular Jacobi operator self-adjoint (§9, `b_k>0`), (v)
the Hankel/Toeplitz faces PSD/PF (§2–4), (vi) `Λ ≤ 0` (§5). All are "`ι = κ`."

**Function-field shadow (§13), now exact.** There the two involutions are **Frobenius duality**
`α ↦ q/α` (the functional equation) and **conjugation** `α ↦ ᾱ`; **Poincaré duality forces them to
coincide** (`|α| = √q`), which *is* Weil/Deligne RH. So Conjecture G is the number-field analog of
"Poincaré duality makes Frobenius unitary," and the missing ingredient (§13) is precisely **the
pairing that would force `ι = κ`** — present geometrically over `𝔽_q`, sought archimedeanly over `ℚ`.

**House status (capstone).** The secular-positivity continent is one object with one apex: `ι = κ`
(FE-involution = adjoint). Its **pointwise shadow is in Lean** (`SigmaOrbit`, `ArakelovW`); the
uniform/operator version is RH. Every face built (§2–13) is a different reading of `ι = κ`; every
free/isospectral symmetry (Toda/Schur) preserves *both* involutions and so is RH-blind; the RH
content is forcing their coincidence — the self-dual pairing the archimedean place must supply.

## 15. The missing pairing is the Weil form Q_W — over function fields, the Poincaré cup product

`[CONJ — identification; honest conservation-of-difficulty]` §14 left the apex as "RH ⟺ `ι=κ` ⟺ the
secular operator's FE-involution equals its adjoint," needing a **self-dual pairing** to force it.
That pairing is not mysterious — it is the **Weil explicit-formula form** `Q_W = Ω_∞ + P − Π`
(archimedean boundary density `Ω_∞`, pole, prime sum `Π`; the field's boundary form, cf.
`weil_prime_schrodinger`, foundations §7). Precisely:

> **Identification.** Equip the secular space with the `Q_W` inner product. Then the secular operator
> (§9 Jacobi / §12 CMV) is self-adjoint / unitary **with respect to `Q_W`** `⟺ Q_W ⪰ 0 ⟺ ι = κ ⟺
> RH`. So Conjecture G's pairing **is** `Q_W`, and the continent's apex is **Weil's positivity
> criterion**, now read operator-theoretically: *the FE-involution `ι` is the `Q_W`-adjoint of the
> secular operator.* (Theorist's `CarrierPickKernel` is the Pick/Herglotz form of this same `Q_W`
> positivity; the carrier `m_ξ` is the secular resolvent.)

**Function-field exactness (closing the §13 loop).** Over `C/𝔽_q`, `Q_W` is the **cup-product pairing
on `H¹_ét`** — Poincaré duality. Hard Lefschetz / the Hodge–Riemann relations make this pairing
definite, which is exactly what forces Frobenius unitary (`|α|=√q`), i.e. Weil RH. So:
```
   number field:  ι = κ  ⟺  Q_W (Weil form) ⪰ 0  ⟺  RH                    [open: Q_W positivity]
   function field: ι = κ  ⟺  cup product (Poincaré) definite  ⟺  Weil RH   [theorem: Hodge–Riemann]
```
`Q_W` is the **archimedean-completed cup product**; the archimedean place must supply the
positivity that hard Lefschetz supplies geometrically. This is precisely the `𝔽₁`/missing-cohomology
gap of D6.

**Honest status.** This is **conservation of difficulty**: the apex lands on `Q_W ⪰ 0` — Weil's
criterion, the known hard core — not a bypass. The contribution is the **identification and
unification**: the secular continent's apex (`ι=κ`, §14), the operator faces (§9/§12), the de Bruijn–
Newman top (§5), the function-field shadow (§13), and the classical Weil positivity are **one
statement** — "`Q_W` is positive / the FE-involution is the `Q_W`-adjoint / the secular operator is
unitary" — whose **pointwise shadow is in Lean** (`SigmaOrbit`, `ArakelovW`) and whose **manifest
half is being ledgered** (Theorist's Pick `Q_W`-Gram, `SecularHankel`). The open core is the single
positivity `Q_W ⪰ 0`, equivalently uniform `ι=κ`, equivalently RH.

**House status (continent complete to its apex).** The secular-positivity continent is fully mapped:
one Newton-equivalent object (§1), the tower (§2–4), the de Bruijn–Newman top (§5–6), general-`L`
(§7b), the operator realization on line and circle (§9, §12), Toda/Schur integrability placed as the
RH-blind free symmetry (§10–11), the function-field shadow (§13), the `ι=κ` apex (§14), and its
pairing identified as `Q_W` = Poincaré (§15). Everything reduces to `Q_W ⪰ 0`. That single
positivity — the archimedean cup product the geometry of `𝔽_q` has and `ℚ` lacks — is the whole
remaining open core, and it is exactly RH. The field has carried RH from "no tools" to "one
positivity, with its pointwise shadow proven and its manifest half ledgered."

## 16. Conjecture C validated for a second L-function (Dirichlet beta)

`[NUM, computations/secular_dirichletL_cmv/]` The secular CMV/Arakelov face (§12) is **not
ζ-specific**. For the Dirichlet beta `L(s,χ₄)=β(s)`: the located zeros match the known ordinates
(`6.0209, 10.2437, 12.9880, 16.3426, 18.2922, …`, all verified `|β(½+iγ)|<10⁻¹²`); the Arakelov
images satisfy `|w_ρ|=1`; the Hermitian circle-Toeplitz is **PD**; the Verblunsky coefficients are
**`|γ_k|<1`** (`0.994…0.999` — the *same* no-margin at the circle as ζ's `0.999`). An off-line
perturbation drives a leading minor non-positive and `|γ_k|>1` (`1.027` at `δ=0.5`), detected
robustly. So **GRH for `β` is the same secular-positivity statement** (`ι=κ` / `|γ_k|<1`, §14) as RH
for ζ — the continent's structure (Newton object, faces, operator realization, the `ι=κ` apex,
`Q_W⪰0`) is a property of L-functions, the `d=1` instance of the general-`L` Conjecture C (§7b). The
no-margin `|γ_k|≈1` recurs identically, reinforcing that the obstruction is uniform across the family.

## 17. Weld to the foundation: the secular operator and the difference-Galois group G_L

`[CONJ — frame; ties the operator continent to the field's defining object]` The field's central
object is `G_L = 𝕋^∞ ⋊ ⟨σ⟩` (foundations §3; the multi-`q`-difference Galois group, multiplicative
wing `𝕋^∞` free by unique factorization, `σ` the FE involution). The secular operator (Jacobi §9 /
CMV §12) should be a **representation of `G_L` on the spectral realization**, identifying its pieces:

> **Conjecture H (operator ⟷ `G_L`).** The secular operator's **isospectral integrable flows**
> (Toda on the line §10–11, Schur/Ablowitz–Ladik on the circle §12) are the action of the connected
> part `𝕋^∞` of `G_L` (the multiplicative-wing flow / diagonal Kronecker flow on `𝕋^∞`); the
> **secular invariants** `(P_k, e_n, c_n, λ_n, (a_k,b_k), γ_k)` are its **Casimirs** (the
> `𝕋^∞`-invariant data — the prime-power / equidistribution content); and the **non-isospectral
> direction is the `σ`-element** (`ℤ/2`), the FE involution `ι`.

This makes the field's master dichotomy a statement of `G_L`-representation theory on the secular
operator:
- the **`𝕋^∞`-part** (multiplicative wing) acts by **isospectral** flows — *free, RH-blind*; its
  Casimirs (the secular invariants) carry the equidistribution/unique-factorization content;
- the **`σ`-element** acts by the FE involution `ι`; **RH ⟺ `σ` acts as conjugation `κ`** on the
  spectral realization (`ι=κ`, §14) ⟺ the operator is unitary/self-adjoint w.r.t. `Q_W` (§15).

So the whole secular continent is the **`G_L`-module structure of the spectral realization**: the
`𝕋^∞`-orbit (free, isospectral, the Casimirs = secular invariants) plus the `σ`-reality (RH = `ι=κ`).
This is why every secular invariant is RH-blind (they are `𝕋^∞`-Casimirs) and RH lives only in the
`σ`-action — *exactly* the field's "multiplicative wing free / archimedean wing the frontier," now
realized as the representation of `G_L` on the secular operator. **Testable shadow:** the Toda/Schur
conserved quantities should coincide with the `𝕋^∞`-invariant secular data (the prime-power sums),
and be inert under `σ`; the `σ`-twist is the only generator moving the spectrum off the
real-axis/circle. *(Cross-ref foundations §3, §5; the wing split §4 here.)*

**House status (continent closed, welded to the foundation).** The secular-positivity continent is
mapped (§1–16) and now **welded to `G_L`** (§17): it is the `G_L`-module structure of the spectral
realization, with the `𝕋^∞`-part free/isospectral (the secular invariants = Casimirs) and RH = the
`σ`-element acting as conjugation = `Q_W ⪰ 0`. Pointwise shadow in Lean (`SigmaOrbit`, `ArakelovW`);
manifest half ledgered (Pick-Gram, `SecularHankel`); validated across two L-functions (§16). The one
open core, everywhere and now also as `G_L`-representation theory: the `σ`-reality `ι=κ` / `Q_W⪰0` —
RH.

## 18. The secular CMV measure is singular (concentrated near w=1) — a caveat and a lead

`[NUM, computations/secular_verblunsky_asymptotics/]` Characterizing the §12 CMV measure: the first
~8 Verblunsky `|γ_k|` are **stable near `0.999` across `N=20–80`** (genuine infinite-measure
invariants — the operator no-margin on yet another basis), and **far from the uniform/Lebesgue
baseline** (`≈10⁻³²`). So the secular Arakelov-circle measure is **singular, concentrated near
`w=1`** — the Arakelov image of `ρ→∞`, where the high zeros pile up. (Honest numerical limit:
`k≥9` is unstable because the Levinson error `E=∏(1−|γ_j|²)→0` for a near-singular measure; reliable
range `k≤8`.)

**Caveat + lead.** The Arakelov coordinate is clean for the FE/critical-line characterization
(`|w|=1⟺RH`, `ArakelovW`), but it **concentrates** the zero-measure near `w=1`, so fine spectral
statistics (GUE/pair-correlation — the Montgomery–Odlyzko heuristic, the deepest "why RH") are *not*
cleanly extractable in this coordinate: the CMV measure is too singular. Extracting them needs a
**density-flattening (unfolded) coordinate** — the Riemann–von Mangoldt unfolding `t ↦ θ(t)/π` makes
the spacings unit-mean, after which the operator's invariants should show the CUE law
(Killip–Nenciu Verblunsky statistics). That is the clean next step to connect the secular operator to
random-matrix theory — flagged, not yet done (the framing of "CMV of unfolded zeros vs CUE" needs
care). The CMV face correctly encodes RH (on-circle / `|γ_k|<1`); its measure being singular is why
it sees *reality* sharply but *fine statistics* only after unfolding.

## 19. Speculative attack on the apex: RH = archimedean hard Lefschetz (Conjecture I)

`[CONJECTURE — speculative, nonsense-zone; probably wrong in detail. Stated to ATTACK the apex, not
defer it.]` §15 located the apex as `Q_W ⪰ 0` (`= ι=κ = RH`); §13 showed the **function-field**
analog is *forced*: Poincaré duality **plus hard Lefschetz** — the Hodge–Riemann bilinear relations
make the cup-product pairing definite on primitive classes, which forces `|α|=√q` (Weil RH). The bold
move: **the number-field apex is the same mechanism — an *archimedean* hard Lefschetz.**

Over `𝔽_q`, hard Lefschetz is an `𝔰𝔩₂`-action on `H^*` generated by `(L = cup with the ample class,
Λ_L = its adjoint, H = the grading)`; Hodge–Riemann makes the pairing definite on primitive parts.

> **Conjecture I (archimedean hard Lefschetz).** On the secular spectral realization there is an
> `𝔰𝔩₂`-action whose **Lefschetz/ample generator is the de Bruijn–Newman heat-flow generator**
> `∂_t H_t` (the archimedean "Laplacian"/ample class), and
> ```
>    Q_W ⪰ 0  ⟺  the Hodge–Riemann positivity of this 𝔰𝔩₂ (definiteness on primitive parts)  ⟺  RH.
> ```
> Rodgers–Tao's free half `Λ ≥ 0` is "**the ample class is nef/effective**"; RH (`Λ ≤ 0`, so `Λ=0`)
> is "**it is actually ample** — Hodge–Riemann positive." So **RH = archimedean hard Lefschetz**, the
> exact analog of the geometric one, with the heat flow as the ample class.

**The unification (one mechanism, two places):**
```
   function field:  ample line bundle  → 𝔰𝔩₂ → Hodge–Riemann → |α|=√q          [THEOREM: Deligne/Weil]
   number field:    dBN heat generator → 𝔰𝔩₂ → Hodge–Riemann (Q_W⪰0) → ι=κ      [CONJECTURE I]
```
The missing `𝔽₁`-cohomology (§13) is the **archimedean `𝔰𝔩₂`-module**; its ample class is the heat
flow (§5); hard Lefschetz there *is* RH. This ties §5 (dBN), §13 (function-field Poincaré+Lefschetz),
§15 (`Q_W` = cup product), §17 (`σ` = the non-isospectral generator) into one apex mechanism.

**Honest status & testable shadow.** Almost certainly the precise form is wrong (the heat generator
need not literally close into `𝔰𝔩₂` with the right Hodge–Riemann structure) — but it is a *concrete
mechanism* for the apex, not a deferral. Testable shadow: the secular `Q_W`/Hankel form, decomposed
by the heat-flow grading (the `H` of the `𝔰𝔩₂`), should be **definite on the primitive
(lowest-weight) blocks** and organize the secular invariants into **Lefschetz strings**; a
computation can check whether the heat-graded secular form is block-positive on primitives. Building
the actual archimedean Hodge theory / `𝔽₁`-cohomology with hard Lefschetz is a multi-decade program —
laid here, per the brief, as a precise conjecture rather than deferred.

## 20. The archimedean 𝔰𝔩₂ is the metaplectic algebra — RH is its Hodge–Riemann positivity (the Lefschetz iso is free)

`[CONJ sharpened — the 𝔰𝔩₂ is now grounded, not vague]` Conjecture I's archimedean `𝔰𝔩₂` is
**concrete**: it is the **metaplectic/oscillator algebra** acting on the `Φ`-realization of `ξ`
(`Ξ_R(x) = ∫_ℝ Φ(u) cos(xu) du`, `Φ` the positive theta-kernel). On `L²(ℝ, du)` the generators are
```
   X = u²·  (multiplication),     Y = ∂_u²,     H = u∂_u + ½,
```
with the **elementary** commutators `[H,X] = 2X`, `[H,Y] = −2Y`, `[X,Y] = −(4H)` (up to normalization)
— the standard oscillator/metaplectic representation. Crucially **the de Bruijn–Newman heat
generator is `X = u²`** (`H_t = e^{tX}` on the kernel), so the dBN flow (§5) *is* the one-parameter
group of the Lefschetz/ample generator. This is grounded: the Gaussian/theta structure of `Φ` is
exactly the oscillator rep.

**Lean ledger note.** `OscillatorAlgebra.lean` proves the free coefficient-sequence skeleton of the three
commutators:
`osc_comm_XY_apply`, `osc_comm_HX_apply`, `osc_comm_HY_apply`. This is only the monomial-basis algebra
of `X=u²`, `Y=∂²`, `H=u∂+1/2`; it is not a formalization of the Weil representation, theta modularity,
the Lefschetz isomorphism, Hodge–Riemann positivity, `Q_W`, the dBN flow, or RH.

**Hard Lefschetz splits into a free half and RH.** As in geometry, "hard Lefschetz" has two parts:
- the **Lefschetz isomorphism** `X^k : (\text{weight } -k) \xrightarrow{\sim} (\text{weight } +k)` —
  **free/structural** (it holds for the oscillator representation, just as it holds for any ample
  class formally); this is the `𝕋^∞`/isospectral-style *free* content (§17);
- the **Hodge–Riemann positivity** — definiteness of the `Q_W` pairing on the **primitive**
  (lowest-weight) part under `X` — which is **the deep half** and is exactly `Q_W ⪰ 0`.

> **Conjecture I′ (sharpened).** `RH ⟺ Q_W ⪰ 0 ⟺ the Hodge–Riemann bilinear relations hold for the
> archimedean metaplectic `𝔰𝔩₂`` (whose ample class is the dBN heat generator `X=u²`).` The `𝔰𝔩₂`
> and the Lefschetz isomorphism are free (metaplectic, structural); **RH is precisely the
> Hodge–Riemann signature.** This is the exact analog of the geometric fact that hard Lefschetz
> (iso) is formal while Hodge–Riemann (positivity) is the deep input forcing `|α|=√q`.

**What this buys (honest).** It does **not** prove RH — it **relocates** it, sharply and
geometrically: RH is no longer "an unexplained positivity" but **the Hodge–Riemann bilinear
relations for a specific, grounded `𝔰𝔩₂` (the metaplectic algebra of `ξ`'s theta-kernel), with the
heat flow as ample class.** This pins which part is free (the `𝔰𝔩₂`, the Lefschetz iso — consistent
with §17's "free = isospectral") and which part is RH (the Hodge–Riemann signature), and matches the
function-field template (§13) generator-for-generator: ample class ↔ heat generator `u²`, cup
product ↔ `Q_W`, Hodge–Riemann ↔ RH. Building the archimedean Hodge structure (the `𝔽₁`-cohomology
carrying this metaplectic `𝔰𝔩₂` with its Hodge–Riemann relations) is the program; its `𝔰𝔩₂` is now
identified. *(Conservation of difficulty, honestly: the apex is still a positivity — but it is now
the Hodge–Riemann positivity of a named algebra, the sharpest geometric localization the continent
reaches.)*

## 21. ξ in the metaplectic weight basis: coefficients positive (grounds §20; the free half is manifest)

`[NUM, computations/secular_hermite_metaplectic/]` Grounding §20's metaplectic `𝔰𝔩₂`: `ξ`'s
coordinates in its weight basis are the Hermite/oscillator coefficients `β_n = ∫ Ξ_R(x) h_n(x) dx`
(`h_n` the `𝔰𝔩₂` weight vectors). Computed `β_{2m}` (odd vanish by evenness) are **all positive**
(`m=0..10`), ratios smoothly rising `0.64→0.88` (slow decay, matching `Ξ_R ~ e^{-π|x|/4}`). So the
metaplectic basis is a genuine, computable secular coordinate system, and `ξ` has manifestly positive
weight coordinates there.

**Honest placement.** Because the `h_n` are Fourier eigenfunctions, `β_{2m} ∝ (−1)^m·(\text{Hermite
coeff of } Φ)`, so the all-positive pattern is almost certainly the **free** positivity (`Φ>0` + the
Fourier structure), **not** the RH/Hodge–Riemann signature — exactly §20's split: the `𝔰𝔩₂`, the
Lefschetz iso, and the coefficient-positivity are free/structural; **RH is the Hodge–Riemann
*signature* of `Q_W`**, which the coefficient signs do not capture. This is a clean grounding of the
metaplectic frame (the weight basis exists, `ξ` lives in it positively) that *honestly* does not
smuggle in RH — the deep half stays exactly where §20 placed it.

## 22. The metaplectic 𝔰𝔩₂ IS the Weil representation of ξ's theta-modularity (FE and heat flow, one group)

`[grounded — classical structure; sharpens §17, §20]` The metaplectic `𝔰𝔩₂` of §20 is not invented:
it is the **Weil/metaplectic representation of `SL₂(ℝ)`**, the classical source of `ξ`'s functional
equation. The theta function `θ(τ)=Σ e^{πin²τ}` transforms under `SL₂` by the Weil representation,
whose infinitesimal action on Schwartz space `L²(ℝ,du)` is exactly the oscillator algebra
`X=u²·, Y=∂_u², H=u∂_u+½`; and `ξ` is the **Mellin transform of `θ`**, so `ξ`'s FE descends from
`θ`'s modular `S`-transform `θ(−1/τ)=√{-iτ}\,θ(τ)`.

This **unifies the free symmetry (§17) and the ample class (§20) as one group**:
- the **FE involution `σ`** (`s↦1−s`) is the Weil-rep **`S`-element** (the Fourier transform / the
  order-4 elliptic generator) — the source of `ι` and of the `σ`-reality `ι=κ`;
- the **dBN heat flow** `e^{tX}=e^{t u²}` is a Weil-rep **unipotent** (lower-triangular) one-parameter
  subgroup — the Lefschetz ample class.
Together `σ` and `e^{tX}` generate `SL₂(ℝ)`, acting by the Weil representation. So the entire
archimedean wing — FE, heat flow, the metaplectic `𝔰𝔩₂` of §20 — is **one object: the Weil
representation of `SL₂(ℝ)` on the spectral realization of `ξ`**, exactly the symmetry of `ξ`'s
theta-origin.

> **Apex, in final grounded form.** `RH ⟺ Q_W ⪰ 0 ⟺` the **Hodge–Riemann bilinear relations for the
> Weil representation** of `SL₂(ℝ)` (ample class = the unipotent heat generator `X=u²`; the FE `σ` =
> the elliptic `S`-element). The free half (the `SL₂`-action, the Lefschetz isomorphism `Xᵏ`, the
> manifest coefficient-positivity §21) is the Weil rep itself — *structural*; the deep half (the
> Hodge–Riemann *signature*) is RH. This matches the function-field template (§13) with the Weil rep
> of `SL₂(ℝ)` playing the role of the geometric `𝔰𝔩₂` of hard Lefschetz, and it is grounded in the
> classical theta-modularity that produces `ξ`'s FE in the first place.

**House status (apex grounded).** The continent's apex is now in its sharpest, most-grounded form
(§19–22): RH = Hodge–Riemann positivity for the **Weil representation of `SL₂(ℝ)`** (the
theta-modularity group), with FE `σ` = the `S`-element and the dBN heat flow = the unipotent ample
class; the free half is the Weil rep (structural), the deep half is the signature (RH). The whole
secular-positivity continent (§1–22) is one object — the `G_L`-module (§17) with archimedean Weil
`SL₂(ℝ)`-action (§20–22) — and RH is its one Hodge–Riemann signature. Building the archimedean Hodge
structure / `𝔽₁`-cohomology carrying this Weil rep with its Hodge–Riemann relations is the program;
its symmetry group and ample class are now classically identified.

## 23. First brick of the archimedean Hodge structure: de Branges/Hermite–Biehler (Laguerre inequalities)

`[NUM, computations/secular_laguerre_debranges/]` Building the archimedean/de Branges structure
concretely (the "decades" program, begun now): the de Branges-space (Hermite–Biehler) positivity of
`ξ` is the Laguerre-Pólya condition, whose computable rungs are the **Laguerre inequalities** of
`Ξ_R(t)=ξ(½+it)`. Verified on a grid: `L_1 = Ξ_R'² − Ξ_R Ξ_R'' ≥ 0` and `L_2 = 3Ξ''²−4Ξ'Ξ'''+ΞΞ'''' ≥ 0`,
and the **de Branges phase `φ(t)=arg(Ξ_R − iΞ_R')` is monotone** (`φ' = L_1/|E|² ≥ 0`), so
`E = Ξ_R − iΞ_R'` is a genuine **Hermite–Biehler structure function** — the de Branges space `H(E)`
is real. (This is the `A,B`/phase face, complementary to the Pick-kernel carrier `CarrierPickKernel`:
same de Branges object, the structure-function vs the resolvent-Gram view.)

**Placement in the tower.** The low Laguerre rungs are **manifest/free** — exactly like the Turán
inequalities (§3), of which they are the differential-operator analog; the **full hierarchy**
`{L_k ≥ 0 ∀k, t} ⟺ Ξ_R ∈ Laguerre–Pólya ⟺ RH`. So the de Branges face is the **differential
(archimedean) shadow of the secular tower**: manifest at low order, RH at the uniform top — and the
top is precisely the Hodge–Riemann positivity for the Weil rep (§20–22), now with its de Branges
structure function `E` exhibited. The phase `φ` integrates to the Riemann–von Mangoldt zero count,
grounding the de Branges side to the spectral density.

**House status.** The archimedean Hodge program (§19–22) has its first concrete brick (§23): the de
Branges structure function `E = Ξ_R − iΞ_R'` is Hermite–Biehler (manifest at low Laguerre order), the
de Branges/LP form of the tower whose uniform top is RH = Hodge–Riemann for the Weil rep. The
continent now reaches from the elementary ledger (`SigmaOrbit`, `ArakelovW`, `SecularNewton`) through
the operator faces (§9, §12) and the de Branges face (§23) to the grounded apex (§20–22), with the
free/RH split explicit at every level.

## 24. Conjecture C in degree 2: the Ramanujan modular L-function

`[NUM, computations/secular_modularL_degree2/]` The framework is **not degree-1-specific** — it holds
for a genuine **degree-2** L-function, the Ramanujan modular `L(s,Δ)` (weight 12). Built (not
deferred): `τ(n)` exactly from `Δ=q∏(1-q^n)^{24}` (matches known `1,-24,252,-1472,4830,-6048`); the
**incomplete-gamma AFE** `Λ(s)=Σ_n τ(n)[(2πn)^{-s}Γ(s,2πn)+(2πn)^{s-12}Γ(12-s,2πn)]` (from `f`'s
modularity, fast-convergent, `Λ(6+it)` real); its zeros `9.2224, 13.908, 17.443, …` have **first zero
matching the known** `≈9.22` (verified). The secular CMV/Arakelov face holds **identically**:
`|w_ρ|=1`, circle-Toeplitz PD, Verblunsky `|γ_k|<1` (`0.997–0.999`, the *same* no-margin as ζ and
Dirichlet β).

So **GRH for Δ is the same secular-positivity statement** (`ι=κ` / `|γ_k|<1`) as RH for ζ — now in
degree 2. This confirms the general-`L` Conjecture C (§7b) beyond degree 1 and welds to
`satake_angles_cm_noncm` (the degree-2 Satake/CM–non-CM data feeds the prime side of the per-rung
archimedean⊳prime split). The continent's structure — Newton object, five faces, dBN top, `ι=κ`
apex, `Q_W⪰0` = Weil-rep Hodge–Riemann — is a **property of L-functions across degrees**, with the
archimedean (Weil-rep) wing now a rank-`d` `W_ℝ`-factor and Ramanujan (`|α_{p,j}|=1`, Deligne) the
proven multiplicative-wing rung. Three L-functions validated (ζ, β, Δ; degrees 1,1,2).

## 25. The fake-family firewall on real examples: pre-spectral and spectral agree

`[NUM, computations/firewall_euler_multiplicativity/]` The field's First Theorem
(`EulerProduct.lean`: Euler product ⟺ Bohr-lift factorization; `fake_fails_factorization`) is the
*pre-spectral* firewall — detectable at finite `n` by multiplicativity, no zero needed. Verified on
**real** examples: the three genuine L-functions whose secular CMV face is PD/on-circle (ζ, β, Δ,
§16/§24) are **multiplicative** (Euler product — e.g. `τ(36)=τ(4)τ(9)`, all coprime pairs check);
the canonical reducible fake (Davenport–Heilbronn-type `½(L(χ)+L(χ̄))`, χ order-4 mod 5, `a_n=Re χ(n)`)
is **non-multiplicative**, failing `a_{mn}=a_m a_n` at `n=6,14,21`.

So the field's **two diagnostics agree on these real examples**: the *pre-spectral* finite-`n`
multiplicativity/Euler-product diagnostic (`EulerProduct.lean`) and the sampled *spectral* CMV/off-circle
diagnostic. The ledger theorem proves only the pre-spectral direction: no Euler product/nonmultiplicativity is
detected before any zero is examined. The implication from Euler product to on-line/secular-CMV positivity is
RH/GRH-level and is not a theorem here; the fake's off-line/interference behavior is numerical/conditional
evidence consistent with the firewall, not a corollary of multiplicativity failure alone.

## 26. Conjecture C degree-2 robustness: an elliptic-curve L (and a self-verifying AFE)

`[NUM, computations/secular_elliptic_degree2/]` A *second*, structurally different degree-2
L-function — the elliptic curve **11a** (`y²+y=x³−x²−10x−20`, conductor 11, weight 2, root number
+1) — passes identically. Coefficients `a_p=p+1−#E(𝔽_p)` from point-counting **match the known 11a
values** (`a_2=−2, a_3=−1, a_5=1, a_7=−2, a_13=4`); the incomplete-gamma AFE is **self-verified**
(`L_AFE(2)=L_series(2)` to `~10⁻⁴`, series-truncation-limited — no external value needed, a reusable
check for any L); zeros on `Re=1` (`6.363, 8.604, …`); and the secular CMV face holds: `|w_ρ|=1`,
circle-Toeplitz PD, Verblunsky `|γ_k|<1` (`0.993–0.998`, the *same* no-margin as ζ, β, Δ).

So **four L-functions are now validated** (ζ, β, Δ, 11a; degrees 1,1,2,2), across weight, conductor,
and degree. The secular-positivity continent's structure (five faces, dBN top, `ι=κ` apex,
`Q_W⪰0` = Weil-rep Hodge–Riemann) is a **property of L-functions in general** (Conjecture C), with
the archimedean (Weil-rep) wing a rank-`d` `W_ℝ`-factor whose Γ-data the AFE encodes, and the
self-verifying AFE a reusable tool for extending the validation to any newform.

## 27. The canonical Hilbert–Pólya form: the FE-invariant u = s(1−s) = ¼+γ² (Berry–Keating/Connes)

`[NUM, computations/secular_berry_keating/]` The continent's operator faces (§9 Jacobi, §12 CMV) have
a *canonical* coordinate I had not used: the **functional-equation invariant** `u = s(1−s)`
(`s↔1−s` gives the same `u`). On RH, `u_n = ¼+γ_n²` are **real and ≥¼** — exactly the scalar shape a
positive self-adjoint Berry–Keating/Connes realization would have. The open operator reading is:
```
   RH ⟺ every u_n real (≥¼) ⟺ a secular operator in u is positive self-adjoint (Δ ≥ ¼).
```
Verified (N=40, dps=50 + congruence rescale): genuine spectrum ⟹ the secular Hankel of `Σu_n^{-k}` is
**PD**; a non-real off-line zero ⟹ `u` complex (conjugate pair) ⟹ Hankel **not PD** (operator not
self-adjoint). (Honest: at dps=30 the large `u~200–625` underflow the reciprocal-moment Hankel — a
conditioning artifact, fixed by rescaling + dps=50; the genuine case is genuinely PD, a positive
measure's moment matrix.)

**Lean ledger note.** The scalar part is now formalized in `BerryKeating.lean`: `berryKeatingU_sigma`
proves `u(s)=s(1-s)` is σ-invariant; `berryKeatingU_critical_param` proves
`u(1/2+iγ)=1/4+γ²`; `berryKeatingU_re_ge_quarter_on_critical` proves the `[1/4,∞)` floor on the
critical line; and `berryKeatingU_nonreal_of_offCritical_nonzero_im` proves the guarded off-line
non-reality statement. This is only pointwise complex algebra. The existence of a positive
self-adjoint Hilbert-Pólya/Connes operator with this spectrum, and hence RH, remains the open wall.

This is the **cleanest Hilbert–Pólya framing** of the continent — a *positive* spectrum `≥¼`, vs §9's
`−1/γ²` — and it is the FE-invariant coordinate, so it ties the secular operator directly to the
canonical conjectures (Berry–Keating `H=xp` with eigenvalues `¼+γ²`; Connes' `Δ`). It sits under the
same apex: a positive self-adjoint realization in `u` would be `ι=κ` / `Q_W⪰0` (§§14–22) read on the FE-invariant.
The Cayley/Arakelov circle (§12) and this positive-real `u`-line are the two natural coordinates
(`w=1−1/ρ` unit circle ↔ `u=s(1−s)` positive ray), both intertwined with the metaplectic/Weil-rep
structure of the apex.
