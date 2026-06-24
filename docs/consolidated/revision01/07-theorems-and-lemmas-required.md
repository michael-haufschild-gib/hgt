# 07 — Theorems and Lemmas Required for the Light Tower Claims (Reference Inventory)

> **Scope.** The mathematical *scaffolding* the programme depends on: the theorems and lemmas that
> are **proven** (on paper as BRIDGE results, and machine-verified as axiom-clean Lean bricks), the
> lemma-shapes still **required but open**, and the **classical imports** relied upon. This is the
> toolkit catalog. Grade **BRIDGE** means "reduces to a classical parent when the multi-`q` vocabulary
> is stripped" — proven, but not native. No proof of RH.

---

## §1 — Proven paper theorems (the BRIDGE layer), by the claim they support

| # | Theorem | Statement (core) | Supports |
|---|---|---|---|
| T1 | **constraint-not-flow** | `Λ` fixed by order-2 `ι:s↦1−s` (`ι²=id`, `Fix(ι)={1/2}`; the critical line is `Fix(ι∘conj)`); the Source-B flow's spectrum is `{log p}` (RH-blind), not the zeros | LT3 |
| T2 | **two-sources / σ-orbit-balance** | `a` is CC `⟺ deg_O(a)=0 ∀` σ-orbit; the Γ-multiplier `a_Γ=Γ_ℝ(s+2)/Γ_ℝ(s)=s/2π` has `div=[0]−[∞]`, `deg_ℤ=+1≠0` (unique non-CC place — the gamma-recurrence ratio) | LT2 |
| T3 | **multiplier-dichotomy** | CC `⟹` holonomic (Galois `⊂𝔾_m`); `deg_∞(a)≠0 ⟹` non-CC; non-CC `⟹` hypertranscendental [import Hölder/ADH] | LT2, LT3 |
| T4 | **corank-seam-invariant** | `corank` = one number, three faces (G1/G2/G4); `corank=∞ ⟺ {log p}` ℚ-LINEARLY indep (Baker); `corank=∞ ⇏ trdeg=∞` (linear floor ⊊ algebraic apex) | LT2 |
| T5 | **G3-corank-dichotomy** | infinite-base diagonal holonomic `⟺ corank(Λ)<∞`; `M_ζ`: `Λ={0}`, `corank=∞` | LT2 |
| T6 | **holonomicity-limit-nonclosure** | `M` holonomic `⟺ corank<∞`; every finite truncation holonomic yet `M_ζ` not `⟹ 𝓜 ≠ lim_T 𝓓_T` | LT1, LT4 |
| T7 | **G1-difference-holder** | ζ and arithmetic L satisfy **no finite-order linear `q`-difference equation** (`g=(p^{-1})_p` has ∞-dim Zariski closure when `Λ=0`) | LT3 |
| T8 | **orthogonality-meta-theorem** | RH-positivity = positivity of the FE-polarization = archimedean; the prime category `𝓜` carries **no polarization** (`g_p=g_p^{-1}⟹g_p=±1`, valid only in a connected/idempotent-free scalar host; in a product/projector host `g=2e−1`, `e²=e` gives sector signs — host passport required) | LT1, LT8 |
| T9 | **universal-prime-side-orthogonality** | `s↦1−s ⟹ p^{-s}↦p^{-1}(p^{-s})^{-1}`; FE-involution not a `T_B`-automorphism `⟹` no Source-B polarization of ζ is RH-equivalent | LT8 |
| T10 | **seam-firewall** | no finite-place positivity forces the archimedean positivity (prime block all-CC, archimedean unique non-CC) | LT2 |
| T11 | **seam-two-lattices** | `∂_s` is a relation on `M_ζ` (`∂_s e_m=−(log n)e_m`), a new generator on `M_∞` (`=−½logπ+½ψ(s/2)`); seam = the **digamma residue** | LT2 |
| T12 | **archimedean-prime-cross-term** | FE = cocycle `ρ_∞ρ_ζ=1`, defect `χ(s)=Γ_ℝ(1−s)/Γ_ℝ(s)` **purely archimedean**; `ι_∞` not a module automorphism; `[∂_s,σ_p]=0` | LT2, LT5 |
| T13 | **archimedean-generator-axis-mode** | `σ_p e_m=p^{−m_p}e_m`, `∂_s e_m=−(m·ℓ)e_m`; `∂_s=−Σ_p(log p)θ_p` generates **no combination modes** | LT2 |
| T14 | **explicit-formula-as-constraint** | the constraint is `W(h)=0` (Weil); `Q_W=𝔇`, signature `(1|∞)`; **`RH ⟺ Q_W⪰0 ⟺ κ₋=0`**, obstruction = one archimedean direction `V_arch=Re ψ` | LT8 |
| T15 | **intrinsic-rh-locus-pure-polarized** | `RH ⟺` (M pure+polarized) ∧ `κ₋=0`; `κ₋=#off-line zero-pairs` (faithful Krein–Langer, **not** a measured trace) | LT8 |
| T16 | **phase-cancellation-crux** | large values = order-preserving affine modes `⟨1,r⟩=𝔾_a⋊𝔾_m` (cannot collide roots); RH danger = transverse seam `[𝔾_a,𝔾_m]`; `(logΞ)''=Σ_ρ(½+it−ρ)^{-2}<0 ⟺` concave; off-line quartet `2(a²−τ²)/(a²+τ²)²` | LT6, LT3 |
| T17 | **prime-zero-susceptibility** | `dρ/dε=−n^{−ρ}/ζ'(ρ)`; mirror ratio frequency-independent `⟺ β=½`; `Φ_k(t)=Σ_ρ(½+it−ρ)^{−k}` (susceptibility = curvature) | LT6 |
| T18 | **critical-line-abscissa** | `𝓛(σ)=−Σ_p log(1−X_p p^{−σ})` converges a.s. `⟺ σ>½`; `Var(Re𝓛)~½ log log X` (Selberg CLT) | LT6 |
| T19 | **erosion-cocycle / threshold** | additive Euler cocycle is a bounded `L²`-coboundary `⟺ σ≥½`; soft/variance methods are structurally RH-blind | LT6 |
| T20 | **critical-line-fisher-signature** | `‖ψ(s)‖²=ζ(2σ)` changes signature `+/pole/−` at `σ=½`; Fisher `g=(logζ)''(2σ)~1/(2σ−1)²` | LT6 |
| T21 | **corank-transcendence-continuation** | `trdeg(T_{s_0})≤corank`; over `F_q` exact `corank=1, trdeg=1` (`ln q`) | LT2 |
| T22 | **f1-inversion-stieltjes-collapse** | `trdeg_ℚ{Stieltjes(ζ_S)}=corank_ℚ{log p:p∈S}`; corank-1 `⟹` `γ_n^{(q)}=(B_n^+/n!)(log q)^n`, `trdeg=1` | LT2 |
| T23 | **f1-two-face-criterion** | `F₁ exists ⟺ (D=0) ∧ (corank finite)`; ℚ: `(D=+1, corank=∞)` `⟹` F₁ missing | LT2 |
| T24 | **frobenius-collapse-linear-vs-algebraic** | `{corank=1} ⊊ {trdeg=1}` (witness `{π,π²}`: `trdeg=1`, `corank=2`) | LT2 |
| T25 | **g2/g4/g5-over-F_q** | over `F_q` (corank 1): `trdeg(periods)=dim G` (Papanikolas DSS); `dim W=corank=1` (Deligne–Katz); reflected critical-line constraint unitary `⟺` RH-over-`F_q` (Deligne Weil II) | LT2, LT8 |
| T26 | **dss-lower-bound-orbit-nogo** | the native `G_L`-orbit gives the DSS **upper** bound only; the lower bound (`F^{(T)}(1)=(−1)^T ΣC_a∏(log p)^{a_p}`) is orthogonal to the orbit | LT2 |
| T27 | **stieltjes-log-weld** | Tier-1 (Baker, unconditional): `{γ_n}` and `{log p}` jointly **linearly** inseparable (`c_1=Σβ_p log p`) | LT2 |
| T28 | **koszul-acyclicity** | the multiplicative ∞-prime Koszul stays acyclic **unconditionally** (RH-blind); `RH ⟺` archimedean-completed Koszul acyclic `⟺ ω=0` | LT1 |
| T29 | **li-secular change-of-basis** | `−ξ'/ξ(s)=Σ_{k≥1}P_k s^{k-1}`, `P_k=Σ_ρ ρ^{-k}`; `λ_n=−Σ_j\binom{n}{j}(−1)^j P_j` (triangular ℤ); `ℚ({P_k})⊇{ζ(odd)}` | LT2, LT8 |
| T30 | **reciprocal-divisor reduction `[gpt/proof12; classical moment theory]`** | `Q_0[p]≥0 ∀p ⟹ RH` for the *actual* folded divisor: Hamburger/Riesz ⟹ positive `μ` on `[−R,R]`; the divisor g.f. `G(z)=Σ_α M_α y_α/(1−y_α z)` (meromorphic, poles at `1/y_α`) `= ∫dμ/(1−xz)` (Cauchy transform of a positive real-line measure, holomorphic off `ℝ`) ⟹ no non-real atoms; `μ=ν:=Σ M_α y_α δ_{y_α}` by Weierstrass ⟹ `y_α>0`. The `⟸` half (source-built `Q_0≥0`) stays open. *Reduction only — passes the roleplaying audit; low novelty (= the `⟹` half of the known moment-positivity↔RH, §10.A2).* | bridge §3 |

---

## §2 — The Lean-verified bedrock (axiom-clean bricks)

All machine-verified; axioms `[propext, Classical.choice, Quot.sound]` only.

| Lean name(s) | Machine-proven content |
|---|---|
| `linearIndependent_log_primes`, `logPrime_no_rat_relation` | `{log p}` are ℚ-linearly independent (unique factorization) |
| `finitePrimeLogAnnihilator_eq_singleton` | `{m : Σ_p m_p log p = 0} = {0}` (and every finite slice) |
| `sigma_involutive`, `sigmaConj_fixed_iff_critical` | `σ(s)=1−s` order-2; `σ̄` fixes exactly `Re(s)=½` |
| `norm_cpow_eq_critical_iff`, `boundaryUnitNormalize_norm_eq_one_iff` | `|p^{-s}|=p^{-1/2} ⟺ Re(s)=½` |
| `gammaReal_shift_two`, `gammaRealLogConnection`, `digamma_half_add_one` | `Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)`; `A(s)=−½logπ+½ψ(s/2)`; `ψ(s/2+1)=ψ(s/2)+2/s` |
| `deriv_archimedeanPrimeMode` | `∂_s e_m = −(m·ℓ)e_m` |
| `archimedean-corank-no-collapse` (`primeLogFullSpan_rank_with_archimedean`, …) | adjoining `∂_s` leaves rank `= Cardinal.mk Nat.Primes` (corank stays ∞ — "F₁ is NOT `∂_s`") |
| `koszulD1_eq_zero_iff_additiveCocycle`, `koszulD1_koszulD0_eq_zero` | additive 1-cocycles `= {τ_p a_q = τ_q a_p}`; `d1∘d0=0` |
| `ccGaugeMultiplier_eq_const`, `hasDerivAt_mul_exp_const_ode` | `a=c·σ(g)/g` gauges to constant; `f=g·e^{zλ}` solves the shift ODE |
| `functionField_localFactor_FE`, `functionField_esymm_FE` | `e_k(S)=q^k e_k(S^{-1})`; `∏(1−ωT)` FE-invariant (purity `|ω|=√q` out of scope) |
| `multiPair_carrier_exact_neg_inertia`, `multiPair_carrier_linearIndependent` | **`κ₋(H)=#off-line conjugate pairs`** exactly (Sylvester) |
| `fe_quadruple_kappa_two` | one off-line zero `⟹ κ₋=2` (FE-doubling) |
| `superzeta_coeff_eq_powerSum`, `superzeta_eq_sum_resolvent` | superzeta gen-fn `=Σ_i(1−r_iX)^{-1}`; `k`-th coeff `=Σ_ρ ρ^{−k}=P_k` |
| `powerSum_torelli`, `spectralTorelli_faithful`, `esymm_eq_of_powerSum_eq` | equal first `n` power sums `⟹` equal zero multiset (faithfulness only) |
| `rankOne_noSelfDualMultiplier_of_sq_ne_one` | the rank-1 dual-multiplier obstruction (orthogonality §1) |
| `orbitDegree_*`, `eq_sum_single_sub_base_of_orbitDegree_zero` | finite orbit-degree algebra; degree-0 `⟹` telescoping coboundary |
| `stieltjes_pairing_cauchy_j` | the Stieltjes–log Cauchy-product coefficient `(★)` |
| `bezout_eq_residue_gram`, `bezout_brick` | `A(s)B(t)−A(t)B(s)=(s−t)Σ_j r_j A_j(s)A_j(t)` |
| `satoTate_orthonormal`, `satoTate_moment` | Chebyshev `U_k` orthonormal for `(2/π)sin²θ dθ`; nonzero moments vanish |
| `li_secular_pointwise`, `secular_li_pointwise_inv` | Li ↔ secular triangular change of basis |
| (moment-positivity repo) `sigNeg(scForm[P]) = winding(P) = #inside(P)` | Schur–Cohn inertia = winding = #roots inside (the `berry_argument_principle_bridge_brick`) |

---

## §3 — Required lemma-shapes still needing proof

These are the theorems-to-be the programme explicitly demands; status reflects what exists.

- **L-A. Local pole geometry `[PARTIALLY PROVED]`.** From `ξ'/ξ(s)~m/(s−ρ)+g(s)` near `ρ=β+iγ`,
  derive exact local behaviour of reset-occupation centre, signed phase-space area, observed-volume
  concentration, two-path Berry amplitudes, co-failure. *Proven so far:* the curvature
  `(logΞ)''=Σ_ρ(½+it−ρ)^{-2}`, RH-concavity, and the off-line-quartet window `2(a²−τ²)/(a²+τ²)²`.
  *Needed:* the remaining detectors centred at `β`, making them zero-location detectors.
- **L-B. Completion symmetry / Berry-as-theorem `[OPEN]`.** From `ξ(s)=ξ(1−s)`, prove exact
  left/right relations for `ξ'/ξ` and for the two-path amplitudes at `s=½±δ+it`, turning the observed
  Berry magnitude-equalization into a theorem (*most promising*). Caveat: it may then be FE-content,
  not native HT.
- **L-C. Continuum association operator `[OPEN]`.** Replace discrete σ-lanes by the integral kernel
  `K_q(σ,σ')=Corr(𝟙_{Δ(σ+it)>q}, 𝟙_{Δ(σ'+it)>q})` and prove a **spectral gap** in the nondegenerate
  band for the true field, absent for productized/random controls.
- **L-D. Phase-Sobolev regularity functional `[OPEN]`.** One seminorm `‖∂_t arg(Γ∞+P)‖` (an `H^{1/2}`
  phase seminorm) that **predicts all of Group B** (lifetime, softness, fragility, dissolution, spine)
  for true and controls.
- **L-E. The source-measure bridge `[OPEN CORE]`.** `transport defect confined to seam ⟹ μ_ξ
  supported on seam`, or contrapositive `off-seam zero ⟹ observable off-seam defect`. This is the
  RH arrow (the global confinement Lemma).

---

## §4 — Classical imports relied upon (carried as hypotheses at the Lean stage)

| Import | Used for |
|---|---|
| **Baker–Wüstholz** (lin. indep. of `{log p}`; `\|m·ℓ\|≥γH(m)^{-κ}`) | `corank=∞`; reducibility Lemma R; Tier-1 Stieltjes weld |
| **Hölder 1887** (Γ differentially hypertranscendent); **ADH / Hardouin–Singer** (non-CC `⟹` HT) | T3, T7, the founding negative theorem |
| **Weil explicit formula / Weil positivity** | T14, T8 (RH = FE-polarization positivity) |
| **Connes 1999** (adelic spectral realization of `{γ_n}`) | T1 §4 (zeros are an archimedean spectrum) |
| **Kronecker–Weyl equidistribution; Selberg CLT** | T1 §1, T18 (`½` as a.s.-convergence abscissa) |
| **Papanikolas 2008 (ABP/DSS); Deligne Weil II; Deligne–Katz** | T25 (the `F_q` border, all three faces) |
| **Procesi / Artin** (character-variety trace invariants) | c3-gluing BRIDGE (no cheap native invariant) |
| **Gelfond–Schneider; Nesterenko; Lipshitz 1988** | corank `corank^{(2)}` degree-2 climb; `π,e^π` indep; D-finite diagonal |
| **Krein–Langer** (`m_ξ∈N₀`); **GORZ / Pólya–Jensen** (`det H_d≥0 ∀d ⟺ RH`); **Csordas–Norfolk–Varga** (Laguerre) | T15, the uniform-Hankel apex form, the `d=2` leader |

---

## §5 — The one-line structural summary

> Everything proven (§1–§2) is **BRIDGE / axiom-clean classical**: the weld, the seam, the
> generators, the faithful index `κ₋`, the corank linear floor, the local pole geometry. The
> genuinely *required* but *unproven* lemmas (§3 L-B…L-E) are exactly the native content — the Berry
> derivation, the continuum spectral gap, and the source-measure bridge — and they sit above the proven
> floor, on the holonomy / value-arithmetic side.

---

## Appendix — The constructive "theorems to build" ledger

§1–§4 inventory what is *proven* and the required lemma-shapes. This appendix adds the **faithful-index
spine**: the theorems that must be *constructed* (not merely proven equivalent), complementing the
transport lemmas L-A…L-E.

### The faithful-index spine `[OPEN]`
- **Source-built object theorem.** Construct the Jacobi/Loewner/Krein or Hodge/F1 object from
  Euler / PNT-scale / `Γ` / pole / FE data **without using zero locations**. *Acceptance:* no
  zero-feeding; fake-family separation; finite gates only as consequences, not fitted inputs.
- **Faithful index equality.** `[finite forms promoted / global OPEN]` Show the faithful
  negative-square index equals the off-line zero count for the completed object and stays dust-proof.
  *Acceptance:* density-zero off-line pairs are detected. (Finite anchor: Lean
  `multiPair_carrier_exact_neg_inertia`, §2.)
- **Index vanishing.** Prove `κ₋ = 0` *from* the source-built object. *Acceptance:* not a measured
  trace, not finite-height, not a restatement of Weil positivity.
- **Hodge/F1 realization.** Realize `Q_W` / `K_ξ` / the primitive Schur–Pick object as a source-built
  polarized Hodge or absolute-geometry intersection form. *Acceptance:* supplies the
  signature/polarization theorem rather than assuming it.

### Second-pass required theorems (named build targets) `[OPEN]`
- **Jacobi Gate Atlas theorem** — define the canonical finite Jacobi/Padé/membrane objects on
  completed-ζ source data and prove exactly which source identity each finite gate tests (must
  include Davenport–Heilbronn / conductor-matched fake-family behaviour).
- **Source-built positive-contraction theorem** — build an operator/recurrence from
  Euler/PNT/`Γ`/pole/FE data, prove self-adjoint with spectrum in `[−1,1]` (no zero-feeding, no
  fitted recurrence).
- **Uniform Jensen / Laguerre–Pólya stability theorem** — upgrade fixed-degree Jensen asymptotics to
  all-degree stability placing `ξ` in the Laguerre–Pólya class (handle small-`n`, growing-degree, and
  arithmetic-correction regimes).
- **Completed Krein–Langer carrier theorem** — identify the correct completed generalized
  Nevanlinna / Hermite–Biehler carrier (with `Γ` regularization) and prove `κ = 0 ⟺ RH` for it.
- **Primitive Schur/Hodge bridge theorem** — prove the finite Schur–Cohn / Pick signatures are
  shadows of a polarized Hodge/F1 intersection object (supply the signature theorem from geometry).
- **Fake-family separation theorem** — for each candidate object, prove strong fakes fail at a named
  structural gate.
- **No-margin preservation theorem** — prove the mechanism is compatible with zero spectral margin.

### Required lemmas for experimental upgrade `[OPEN]`
Right-strip collapse control (`Re>1` agreement); strong-surrogate construction (FE-exact/correct-zero
non-HT fake); amplitude-neutralization lemma (statistic not contaminated by `|A+P|`); phase-unwrapping
stability; window/threshold robustness; **no-zero-feeding audit for every zero-localization
statistic**.

### The two dependency chains (two faces of one conjectured theorem)
```
   transport face:   d log ξ object ⟹ canonical source-carrying defect calculus
                      ⟹ off-line zero ⟹ off-seam defect ⟹ defect forbidden
                      ⟹ off-line contour charges vanish ⟹ RH
   faithful-index face: Euler/Γ/FE source data ⟹ source-built faithful polarization/index object
                      ⟹ index = off-line zero count ⟹ index forced to 0 ⟹ RH
```
`[OPEN]` These may be two faces of the same theorem; that equivalence is itself open. (Constructive
counterpart to the apex forms.)

---

## §6 — Refinements of the required lemma-shapes

- **L-A (local pole geometry) — refined.** The off-line window is the same-height mirror pair near
  `t=γ` (conjugate near `t=−γ`); its faithful detector is the **sign-changing scale-matched** kernel
  `C_a(τ)` with matched width `≈a/2`, requiring a height-coverage certificate.
- **L-C (continuum association operator) — refined.** Must be a **cross-lane memory-kernel / Laplace
  family**, not a scalar `top_eig`/`ξ_σ`, and validated against **per-lane-spectrum-preserving**
  (isospectral) controls.
- **L-D (phase-Sobolev functional) — refined.** Add a **guard-band invariance** requirement (single
  windows are edge-contaminable).
- **NEW lemma-shape — affine passport subtraction.** Prove the holonomy carrier equals the affine
  connection's transport **modulo the passport `Π(S)=(|S|,Σm)`** (shift `−|S|log p`); any
  determinant-volume observable is RH-blind until `Π(S)` is subtracted.
- **NEW lemma-shape — sign-changing scale-matched positivity detector.** Prove the off-line curvature is
  detectable only by a zero-mean kernel matched at width `≈a/2`, certifying the APEX-B numerics.
- **NEW lemma-shape — fake separation is the integer `κ₋`, not the scalar `s_d` `[VERIFIED — comp81/72]`.** The
  required fake-family lemma (the `s_d>0` apex, T-D) must be stated on the **index**: a fake can carry `κ₋=2` with
  the rank-one scalar `s_d>0` (comp81: reversed prime sign), so `s_d=0` is only the height-limited shadow. Target
  shape: `Λ(n)≥0` (Euler-product positivity) `⟹ κ₋(H^-)=1` (exactly one negative square) from source; the
  archimedean budget `≈a_*` sits on the prolate Hermite grading `2|w|=4N+1` and matches the Connes–Consani–Moscovici
  archimedean Sonin positivity *unconditionally*, leaving the prime/finite-place demand (the **semilocal** prolate,
  arXiv:2310.18423) as the carrier of the RH content.
- **NEW lemma-shape — the scalar-shadow lemma `[gpt/48]`.** State and prove precisely *when* the rank-one scalar is
  faithful: **`s_d>0 ∧ κ₋(v_*^⊥)=0 ⟺ κ₋=0`** — i.e. `s_d>0 ⟹ κ₋=0` only given `inertia(H^-)=(d,1)` **and** rank-one
  exhaustion of the negative space by `v_*`. (Prevents the scalar from masquerading as the faithful gate; comp81 is the
  countercase.)
- **NEW lemma-shape — finite-rank boundary Weyl over the prolate channels `[gpt/48; tested comp82]`.** Promote
  `a_*v_*v_*^T` to `VCV^*`, `V=(v_0,…,v_r)` the `4N+1` channels `v_N=v(−(2N+½)^{−2})`, `C=diag(a_N)`; the faithful gate
  is the matrix Schur complement `κ₋(S_r)=0`, `S_r=C^{−1}+V^*B^{−1}V`. **comp82 answers the "does finite `r` recover
  `κ₋`?" question:** the `4N+1` basis is **faithful** (every fake's negative direction lies in the channel span) **but
  the rank needed = the defect's height** (sign-fake → `N=0`; off-line zero at `g0` → `N≈g0`-scale), so a finite-`r`
  truncation is height-limited (`d*≈γ0/3`), *not* a finite-rank shortcut. ⟹ the faithful object is the **full
  all-channel** carrier; the lemma must be stated all-order, with finite `r`/scalar `s_d` as height-graded shadows.

---

## §7 — SOTA imports to carry

Additions to §4, reflecting the live literature the open lemma-shapes should build on.

| Import | Used for |
|---|---|
| **Griffin–Ono–Rolen–Zagier (2019)** (fixed-`d` eventual hyperbolicity of Jensen polynomials of `ξ`; asymptotic for central derivatives; GUE) | APEX-B / Conjecture B — the proven fixed-`d` floor under the uniform-in-`d` apex (L-A, the Jensen entrance) |
| **Connes–Consani: arithmetic site (2014); Riemann–Roch for `\overline{Spec ℤ}` (2022); Jacobian of `\overline{Spec ℤ}` (2026); zeta spectral triples; prolate-operator spectral realization** | Master 2 (source-built faithful-index object); Conjecture E (the realization is archimedean/positivity); the `F₁` / `Spec ℤ ×_{F₁} Spec ℤ` program |
| **Adamczewski–Dreyfus–Hardouin** (differential transcendence of difference equations over `ℂ(z)`; Galois proof of Hölder; elliptic extension to Weierstrass ζ, 2024) | Source A/B classifier; the founding negative theorem; the open *weld* is precisely the joint archimedean+prime direction this `ℂ(z)` theory does not reach |
| **Ax–Schanuel for mixed Hodge structures (Gao–Klingler 2023); elliptic Schanuel variations (2025)** | APEX-A context — the geometric/functional Schanuel results, distinct from the open arithmetic statement |

**New lemma-shapes these imports suggest:** (i) *port the GORZ asymptotic* to control the corpus's
APEX-B no-margin instead of brute sub-grid scans; (ii) *identify the corpus's faithful index `κ₋` with
the Connes–Consani Riemann–Roch / prolate spectral data* (would be a concrete attack on Master 2 + the
identification bridge).
