# Mechanisms behind the walls, three focus questions, and a new field

Status: 2026-10-25, corpus checkpoint `e90f915ec` plus the working tree of that day. Inputs: the frontier map, the killed-routes catalogue, the route-unification ledger, the hard-obstacles report, the walls ledger, *what forces blindness*, the 21 programme READMEs, corpus searches (§6), and the work in progress on the strip Bochner–Weil forcing laws, the quantum budget of multiplicative positivity and the closedness of the blind ideal. Research log: `logs/opus-review-2510-2026-10-25.md`. Nothing was compiled. Statements marked *(model)* are model calculations, not proofs.

## 0. Answers in brief

1. **Is there a mechanism that gets behind a wall?** Not one that crosses Wall 1 today. The review finds the common cause of every exhaustion theorem: *depth homogeneity*, together with a split of positivity into *dominated* and *oscillatory payment* (§2.1). This fixes what a crossing mechanism must contain. Two consequences are new:
   - Wall 3 is not an independent wall. Every transfer bridge examined collapses either into zero location or into the near-coincidence problem. The cofactor escape module is the spectral measure of the receiver (§2.3), the blind ideal closes only in topologies that already read the off-line zeros, and selection beyond aperture `½ log Γ` is the near-coincidence problem at one height.
   - There are five candidate mechanisms that the corpus searches did not find, each with a first test (§2.2–§2.6). One immediate result: Tao's logarithmically averaged two-point Chowla theorem settles SSA's open problem 1, though ineffectively.
2. **Three focus questions** (§3), one for each way purity has ever been proved:
   - **F1, the base problem (Deligne).** Can the zeros of ζ be placed in the H¹ of a self-dual coefficient system over a one-dimensional base whose own H¹ vanishes? This is the only known way to turn positivity into a rate without growth input.
   - **F2, signed near-coincidence cancellation beyond the square-root threshold (analytic).** The rate wall, selection, the sub-half Vaughan residual and TTPC are one object.
   - **F3, a section count on the scaling surface (Weil).** It must satisfy Riemann–Roch for oscillatory payment and bound the Hodge defect below its first quantum, `D < 2`.

   These replace the corpus's Q1–Q3; the reasons are in §3.4.
3. **The new field: Arithmetic Künneth Theory** (§4), positivity on products of arithmetic spectra. Its object is the missing Spec ℤ × Spec ℤ, seen through its trace: renormalized products of the explicit-formula distribution. Its point counts are additive (Bézout) prime correlations at the Nyquist scale of the logarithmic grid, and its spectral side consists of tuples of zeros. Weil's surface Hodge index and Deligne's tensor-power estimate are its two purity statements.

## 1. What the reading fixes

Only the facts the arguments below use.

- **Three exhausted mechanisms:**
  - single-channel quadratic positivity, trapped in the maximal blind ideal (`isGreatest_meyerSharpPositiveIdeal`);
  - finite multiplicative certificates, limited by the Fejér barrier `B/A ≤ 2cos(π/(K+2))`, the width `(√B−√A)²/G` and the universal cap `(3−2√2)/(2L)`;
  - linear rigidity: positive measure plus theta law gives ζ, and this does not locate zeros.
- **First-rung coincidence.** Every graded cancellation receiver, and multiplicative forcing, first gains beyond Vinogradov–Korobov at a fixed strip `Θ < 1`.
- **The quantum budget.** In de la Vallée Poussin coupling, a zero of order `m` at distance `η` from `Re s = 1` survives iff `m ≤ b(η) = (√A + √(Gη))²/B`. On the boundary `b(0) = A/B ≤ 1`; at the critical line `b(½) ≥ 1` once the growth constant reaches `L ≥ 2`. The forcing integer of multiplicative positivity therefore has no budget below its first quantum in the strip.
- **Coupled forcing exists and stays at the boundary collar.** Følner sets of ordinate sums `Σ v_ℓ γ_ℓ` give collective repulsion of `r` zeros from `Re s = 1` when `2Σm > κ`, with width `≍ 1/G_k`. The constant `G_k` contains `log(3+T_k)` and the near-resonance sum `Σ (x_j − x_k)^{−2}` over the image set.
- **Pole budget.**
  - Finite corrections of ζ obey `ord₁F − 1 =` inserted multiplicity by frequency pairs.
  - Completed multiplicative gauges collapse to monic polynomials of degree `2κ`.
  - At `κ = 1` no nonnegative Laplace deformation of ξ exists, even with critical refunds.
  - On the `κ`-graded polar surface the defect is `κ(ℓ_Hℓ_V + ℓ_Vℓ_H) − L`.
- **The blind ideal and topology.** The blind ideal is closed in the natural Fréchet topology, unconditionally. In every topology coarser than or equal to the critical-jet topology it is dense; there it is closed iff RH.
- **Escape.** Record-minimum limits, singleton-or-continuum families, the contraction calculus and the rank-one law `η(p)p^{−s}`, `s ≥ ½`, are proved. White noise survives every proved constraint.
- **Averaged positivity.** At aperture `κ₀ log Γ` on `[Γ, 2Γ]` the main term is the local critical-zero weight. Bad phases recur syndetically. Under RH, phase-recurrence gaps grow doubly exponentially.
- **Battery.** Golden datum `1 − 5X + 5X²`; shifted pairs `ζ(s−a)ζ(s+a)`; over-regular Beurling systems; the pole-order 2 and 3 and strip-pole models; parity twins; the theta-power family `θ₃h^{a/4}` (off-line zeros at every transcendental `a`).

## 2. Q1 — mechanisms

### 2.1 Two facts behind every exhaustion theorem

**(a) Dominated versus oscillatory payment.** For a positive source write `−F'/F` as a Mellin transform on `u ≥ 1`. Each term below is a density on `u ≥ 1` that `−F'/F` gains when the stated zeros are inserted and paid for by pole order.

- A real inserted pair `{β, 1−β}` paid by one pole unit at `0` and `1` contributes
  `u^{−1}(1 + u − u^β − u^{1−β}) = u^{−1}(1 − u^β)(1 − u^{1−β}) ≥ 0`.
- A critical pair contributes `u^{−1}(1 + u − 2u^{1/2}cos(γ log u)) ≥ u^{−1}(1 − √u)² ≥ 0`.
- A quartet needs two units, since `2 + 2u − 2cos(γ log u)(u^β + u^{1−β}) ≥ 2(1 − u^β)(1 − u^{1−β})`.

Because Λ_ζ is atomic, this smooth density must be nonnegative on its own. Inserted zeros are therefore paid **by domination**: one pole unit per pair, two per quartet. The finite budget, gauge collapse and `κ = 1` rigidity are complete theorems about this kind of payment.

The zeros of ζ itself are paid differently. In `Λ(n) ≈ 1 − Σ_ρ n^{ρ−1}` (the explicit formula as measures), a single simple pole pays infinitely many zeros, because the zero sum converges only through cancellation. They are paid **by oscillation**. An off-line zero of ζ would be paid the same way: its term `n^{β−1}cos(γ log n)` is `o(1)` against the pole. Three consequences follow.

- **The pole budget has no leverage on intrinsic zeros.** On the `κ`-graded polar surface the defect is independent of `κ` on primitive classes `ℓ_H = ℓ_V = 0`, and pole-free blind tests already detect every off-line zero (the HF receivers). No amount of pole budget pays an intrinsic off-line zero. Wall 14.13 splits accordingly. Its inserted-zero face is closed; its intrinsic face is a statement about how fast oscillatory payment must be made, which is Wall 1.0.
- **Coupling gives only "max" statements.** Collective repulsion says that a coupled family cannot all hug `Re s = 1`. A single off-line zero hidden among critical zeros is not constrained. This is SRT's hiding problem in coupled form.
- **The quantum budget is the integer form of the same fact.** Depth enters only through `√(Gη)`, additively under the root, with nothing that could be amplified.

**(b) Depth homogeneity.** In every mechanism in the corpus, the gain from seeing a zero of depth `δ` and the cost paid for it scale together.

| Mechanism | How depth enters | How cost scales | Outcome |
|---|---|---|---|
| Aperture `a` (Weil, ground energy, AIP, ACS floors) | off-line pair `~ e^{2δa}` | prime/ℓ¹ cost `~ e^{a}` | rate stays `½` without a source estimate |
| Harmonic coupling, degree `K` | twists `n^{−ikt}` are tensor powers of unitary characters: zeros of `ζ(s+ikt)` sit at `ρ − ikt`, same real part | pole fixed, `B/A < 2`, growth `G` grows | width `(√B−√A)²/G`; `b(½) ≥ 1` |
| Coupled Følner forcing | heights add, `Σ v_ℓγ_ℓ`; depth only through `1 − β` | `G_k` grows with height and near-resonances | boundary collar only |
| Family averaging over `χ mod q` *(model)* | primes `≡ 1 (q)` start at `q+1`, so the family form is archimedean to aperture `½ log(q+1)` | zero density rises by `φ(q)`; visibility needs `q^δ ≳ φ(q)` | no `δ ≤ ½` gains |
| k-level correlations / absolute tensor powers *(model)* | a k-tuple of one off-line zero has depth `kδ` | total Fourier support `S` must grow with `k`; Kurokawa's `ζ^{⊗k}` has trivial strip `[0, k]` | `Θ − ½ ≲ 1/S`, independent of `k` |

Proposed theorem shape (**amplification homogeneity law**): for each class above, an `O(1)` bound on the amplified receiver yields `Θ − ½ ≤ c/S`, where `S` is the arithmetic length consumed. The gain is independent of the amplification degree. Each instance is a no-go with a positive survivor, because it names the term that would have to stop scaling.

**(c) What breaks homogeneity in function fields.** Purity for curves has three proofs, and each breaks homogeneity with an ingredient that Spec ℤ lacks.

- **Weil.** Finite genus, plus Riemann–Roch on `C × C` (effectivity), turns Hodge index into Hasse–Weil. Over ℤ the genus is infinite (mildly: `Σ_{|γ|≤T} 1/|ρ| ≍ log² T`) and RR is missing (the ACS open core).
- **Deligne.** The input is positivity of the even tensor powers of a self-dual local system on a **curve**, with the pole part (H²_c) of the tensor powers computed by monodromy invariants. The loss from the one-dimensional base is fixed and disappears after taking 2k-th roots. Over ℤ, ζ's zeros are the H¹ of the *trivial* system on Spec ℤ, and its tensor powers are trivial. Spec ℤ is its own base. Absolute tensor powers have no base, so they are homogeneous (table above).
- **Stepanov–Bombieri.** An auxiliary polynomial vanishes to high order at every `F_q`-point, using `d/dx(x^q) = 0`, with degree bounded by RR. Over ℤ no derivation kills Frobenius.

### 2.2 Mechanism A — the Deligne mechanism, stated as a base problem

**Idea.** Positivity must act on tensor powers of a *coefficient system*, not on ζ's own log-coefficients or on their harmonics. That is the "object outside multiplicative positivity" the quantum budget calls for. In corpus terms the required data are:

- a base `B` with a simple pole and no zeros of its own (`H¹(B) = 0`);
- a self-dual system `F` on `B`, whose even tensor powers have nonnegative log-coefficients;
- a computable pole part of `L(B, F^{⊗2k})`;
- zeros of ζ among the zeros of `L(B, F)`.

With these data the loss is fixed and `Re ρ ≤ ½ + O(1/k)` for every `k`.

**Why it escapes the exhaustion theorems.** It is not single-channel: the tensor powers live on a different carrier for each `k`. It is not a finite certificate, and it is nonlinear in the coefficient measure, since tensor powers are pointwise products of local traces. It sees pole order: the pole part of `F^{⊗2k}` is computed, not assumed. The pole-order models do not fibre over a base with big monodromy.

**Battery.** Over `F_q` it is Weil I. The golden datum cannot be the H¹ of such data (no fibration with big monodromy). Beurling systems have no local systems beyond characters.

**First tests.**
- (A1) The amplification homogeneity law for k-level forms on tempered configurations, using SRT's configuration machinery.
- (A2) Write the base axioms as positive arithmetic data. Calibrate on a hyperelliptic family over `F_q`, then check which axioms the known ℤ-families satisfy: the cyclotomic tower (characters do not mix), Hecke characters, and the theta-power family (killed by no-go-491).
- (A3) Prove that base data definable from multiplicative (Beurling) structure alone are satisfied by over-regular systems with off-line zeros. That would show the base must use additive structure and tie A to C and F2.

**Risk.** The base may not exist. The obstruction theorem would then retire the Deligne mechanism over ℤ, leaving F2 and F3.

### 2.3 Mechanism B — the escape module is the receiver's spectral measure (Wall 3.15 collapses)

**Exact identity.** Put `a(y) = A_ε(⌊y⌋)` (with `A_ε(0) = 0`), `b(u) = e^{−u/2}a(e^u)` and `L = log(T+1)`. The pronic weight is `1/(n(n+1)) = ∫_n^{n+1} dx/x²`, and `⌊⌊x⌋/j⌋ = ⌊x/j⌋`. Substituting `x = e^u` gives

`⟨D_jA, D_kA⟩_T = (jk)^{−1/2} ∫_0^L b(u − log j) b(u − log k) du`, so `K_T(j,k) = (jk)^{−1/2}·⟨τ_{log j}b, τ_{log k}b⟩_{L²(0,L)} / ‖b‖²_{L²(0,L)}`.

Floor dilation is translation on the log line, and the cofactor Gram is a truncated translation Gram of a single function. By Abel summation `b̂(τ) = G(½ + iτ)`, where `G(s) = ζ(s)(1/ζ(s+ε) − 1/ζ(1+ε))/s`; the pole of ζ at 1 cancels.

**Admission** (bounded energy) means `b ∈ L²`, i.e. `G` lies in the Hardy space of `Re s > ½`. Then `K(j,k) = (2π‖b‖²)^{−1}∫ j^{−(½+iτ)} k^{−(½−iτ)} |G(½+iτ)|² dτ`. This is a continuous superposition of characters on `Re s = ½` with a.e. positive density: the faithful module with full Bohr hull.

**Escape** *(model, exact for finitely many top zeros).* `G` has poles at `ρ − ε` for zeros with `Re ρ > ½ + ε` that zero translation does not cancel. Then `b(u) = Σ c_ρ e^{(ρ−ε−½)u}` plus lower-order terms. The energy escapes to the horizon, and every common limit is the Gram matrix of horizon translates of the top profile in `L²(e^{(2σ−1)v}dv, v ≤ 0)`, `σ = Θ − ε`:

`K(j,k) = Σ_{ρ,ρ'} B_{ρρ'} j^{−(ρ−ε)} k^{−(ρ̄'−ε)}`, with `B` positive semidefinite (a Cauchy matrix `1/((2σ−1) + i(γ−γ'))`).

These limits have finite rank when finitely many zeros attain the top. Their diagonal decays like `K_pp ~ p^{−2σ}`, so `pK_pp → 0`. White noise `δ_jk/j` needs effective exponent `σ = ½`, i.e. energy that grows slower than every power.

**Consequence.** Paid kernels vanish at translated off-line zeros to the visible order, so the true escape states are annihilated by the paid ideal automatically. A nonzero paid ideal excludes white noise, but not these states. B3.16 is therefore the question whether `{ρ − ε : Re ρ > ½ + ε}` is a zero set of the critical Wiener algebra, which is about how many off-line zeros exist. Excluding escape through the paid ideal requires every actual module to be faithful, which is exactly the absence of top zeros. Q3 is zero location in module language.

The blind-ideal closedness result has the same structure: the blind ideal closes exactly in topologies that already read the off-line zeros. Wall 3's bridges reformulate; they do not produce.

**Positive survivor.**
- An exact detector: the hull of an actual escape module contains the translated top zeros (target: "hull = top").
- The power-character kernels as the natural escape model in the ADR battery, more faithful than white noise or augmentation.
- The module theory of PM/ADR as the spectral theory of `G`, which can be imported wholesale.

**First tests.**
- (B1) The exact identity (finite, unconditional).
- (B2) Admission ⇒ the Plancherel form above.
- (B3) Power-character kernels with `Re s_i > ½` satisfy every proved ADR constraint, so they form a countermodel family to escape exclusion by those constraints.
- (B4) Finite top ⇒ finite-rank limits. This classifies escape states; it is not an RH input.

### 2.4 Mechanism C — the Nyquist-renormalized Künneth square

**Object.** Let `T(x) = Σ_ρ e^{(ρ−½)x} = (polar + archimedean) − Σ Λ(n)n^{−½}(δ_{log n} + δ_{−log n})`, the explicit formula read as a distribution.
- Its external square `T ⊠ T` on `ℝ²` exists, but its diagonal does not (`δ_{log m}δ_{log n}`): Künneth fails over ℤ.
- At resolution `η`, the smoothed square `∫ T(x)T(x+h)φ_η(h) dh` has prime side `Σ_{|log(m/n)|<η} Λ(m)Λ(n)/√(mn)` and spectral side the pair sums.
- The natural resolution is the Nyquist scale of the logarithmic grid, `η ≍ e^{−x}`, where nearby logarithms are bounded additive shifts. There the square's "point counts" are `Σ_n Λ(n)Λ(n+h)`.
- The diagonal `ρ = ρ'` doubles depth (`e^{2δx}`). The pole part is the singular series `𝔖(h)`, which plays the role of the classes in degree 0 and 4 of `C × C`. Purity of the pair part is Hardy–Littlewood with square-root error, which implies RH.

**Why it is a candidate producer.**
- It is constructed before its sign.
- Positivity is free (`Λ ≥ 0`).
- It uses additive structure, so it is Class III: it satisfies BVI's requirement that a mechanism seeing RH must use Bézout structure, and it fails by construction for Beurling systems, which have no shifts.
- Over `F_q[T]` the dictionary exists. Power-saving twin-prime and Chowla asymptotics for fixed large `q` (Sawin–Shusterman) come from identifying correlation sums with point counts of varieties and applying Deligne; Bary-Soroker proved the `q → ∞` case. Over ℤ the square should be the trace of an "arithmetic configuration space".

**What it lacks.** Its purity is F2.

**First tests.**
- (C1) A renormalization theorem: the `η`-smoothed square minus its diagonal counterterm has a limit at the Nyquist scale. Identify the counterterm and the singular-series pole part.
- (C2) An exact finite identity between the smoothed Weil-form square and shifted prime correlations.
- (C3) A first-rung lemma: absolute-averaged power-saving Hardy–Littlewood in long shift ranges ⇔ `Θ < 1`. This adds the near-coincidence face to the first-rung list and shows that only signed, kernel-weighted forms can be weaker than a strip.

### 2.5 Mechanism D — Class III producers from the literature

**The theorems.**
- Tao's logarithmically averaged two-point Chowla: `Σ_{n≤x} λ(n)λ(n+h)/n = o(log x)` for every fixed `h ≠ 0`.
- Odd-order logarithmic Chowla (Tao–Teräväinen).
- Averaged Chowla (Matomäki–Radziwiłł–Tao). The corpus holds this only as the interface `AveragedChowlaUniform`.

These are the only unconditional theorems giving *signed* successor cancellation for λ or μ.

**Immediate consequence.** At shift 1, `Σ_{n≤M, λ(n)=λ(n+1)} 1/n = ½Σ(1 + λ(n)λ(n+1))/n = (½ + o(1)) log M`. This beats the `1/3` floor, settling SSA open problem 1 ineffectively; the same argument at lag 2 beats the `1/4` floor.

**Limits.**
- These results are at the density scale. Fixed successors vanish under escape normalization (ADR), and the mixed Vaughan entries need power savings (BVI), so this mechanism cannot cross Wall 1.
- Using the theorem in Lean means formalizing the entropy-decrement argument.

**Value.**
- These are the first proved Bézout-selective signed inputs.
- They pose a sharp question for every route: which receiver consumes a density-scale signed shift correlation?
- SSA's floor programme should be retargeted. Effective constants are one option; the square-root-scale successor estimate SSA already lists is the other.

### 2.6 Mechanism E — Stepanov–Baker auxiliary functions (long shot)

**Gap.** Over `F_q`, Stepanov counts points by an auxiliary polynomial vanishing to order `ℓ` at all points. Over ℤ the nearest structures are Siegel-lemma auxiliary functions with integrality and high-order vanishing (the Baker machinery is in the corpus) and Fermat quotients `δ_p(a) = (a − a^p)/p` as an arithmetic derivative.

**Cheap test.** Bound `π(x+H) − π(x) ≤ (2 − c)H/log H` on some range without Type II input. Beating the sieve's parity factor 2 would show that the auxiliary function sees primes. If it cannot, retire the idea. Both halves exist in the corpus (`StepanovCount.lean`, the Baker auxiliary-function modules).

### 2.7 Checked and set aside

| Idea | Disposition | Reason |
|---|---|---|
| Lee–Yang restriction along the archimedean chirp (Gonek-type symmetrized Euler products) | already in corpus | Symmetrized Euler exponentials have their zeros on the line above `2π exp(2ψ(N)+1)`; Lee–Yang data with frequencies `≥ λ₀` have linear counts while Ξ needs `T log T`. The chirp is the survivor; convergence to ζ needs zero location. |
| Fourier-quasicrystal (Dyson) rigidity using "pole part minus positive counts" | killed by battery | Curve zetas have dual weights `q^m + 1 − N_m` with `N_m ≥ 0`. The golden datum has exactly this sign structure and impure zeros. A version must use the archimedean density essentially. |
| Sign-uncertainty and linear-programming magic functions (Bourgain–Clozel–Kahane, Cohn–Gonçalves, Viazovska) | equivalent | Finite-level existence ⇔ RH. A positivity certificate at an aperture is RH at that aperture. |
| Family averaging; absolute pole budget; `κ` as a graded unit | homogeneous or reformulation | §2.1. |
| Continuity in modular families | killed | Theta-power family: every transcendental parameter has off-line zeros. RH-type behaviour is arithmetic, not generic. |

### 2.8 Effect on the walls ledger

| Face | Assessment |
|---|---|
| 1.0 | Unchanged; explained by depth homogeneity. Crossing the first rung needs F1 or F2 input. |
| 3.3, 3.14, 3.15 | Not independent walls. Blind-ideal closure is zero location; selection beyond `½ log Γ` is F2 at one height; the escape states are translated zeros (§2.3). |
| 14.10–14.11 | Coupled positivity exists and is depth-homogeneous. The missing ingredient is a base with a coefficient system (F1). |
| 14.13 | Inserted-zero face closed (dominated payment); intrinsic face = 1.0. |
| New: base | The Deligne mechanism needs a one-dimensional base with `H¹ = 0` beneath Spec ℤ. |

## 3. Q2 — three focus questions

### F1. The base problem

**Question.** Is there a positive arithmetic coefficient system `F` on a one-dimensional base `B` with the four properties of §2.2? If yes, then `Re ρ ≤ ½ + O(1/k)` for all `k`. If no, prove it.

**Why first.**
- It is the only known mechanism that converts positivity into a rate without growth input. Multiplicative positivity has quantum budget `≥ 1` on the critical line.
- Its answer decides whether Wall 1 can be crossed by positivity at all.

**Rungs.**
1. The amplification homogeneity law (A1). Lean target on configurations.
2. Base axioms as positive data, with the `F_q` calibration (A2).
3. A multiplicative no-go (A3), which would show that the base must use additive structure.
4. Candidate search in F₁-type geometries: Connes–Consani scaling site, Deninger flows, Borger λ-rings. Test each against the axioms rather than building more receivers.

**Success** is a base, or a theorem that no base exists in a stated class. **Kill** if the class needed is equivalent to a zero-location hypothesis.

### F2. Signed near-coincidence cancellation beyond the square-root threshold

**Question.** Prove signed cancellation in `Σ_h w(h)[Σ_{n≤X}Λ(n)Λ(n+h) − 𝔖(h)X]` for oscillating kernels `w` (the coalescent kernel of TTPC). The range is shift lengths `H = X^θ` at bandwidth `λ > 1` (`|log(m/n)| < T^{−1+η}`, `X = T^λ`), and the precision must be a power.

**Why.**
- By homogeneity, every depth gain over ℤ passes through near-coincidences of prime-power products. TTPC's coalescent band, selection at one height beyond `½ log Γ`, the sub-half Vaughan residual and the Künneth square are the same object.
- Absolute-averaged versions start at a fixed strip (C3). Only signed forms can be weaker than a strip and still informative.
- Matomäki–Radziwiłł–Tao give averaged Hardy–Littlewood with logarithmic savings for `H ≥ X^{8/33+ε}`. At `λ = 4/3` the coalescent band needs a saving of order `X^{1/4}` over `H ≍ X^{1/4}` *(model count)*.

**Rungs.**
1. The narrow strip `λ = 1 + δ`: `β(δ) ≤ Bδ²/(1+δ)²`.
2. Transfer TTPC's trapezoidal lobe cancellation to `1_ℙ(m)1_ℙ(m+2r)`.
3. Singular-series error against the signed kernel, uniformly in the moving cutoff.
4. Model calibration with an inserted off-line zero, to measure how much signed cancellation is needed.

**Progress unit.** The proportion of simple critical zeros: `β < 5/36` beats `2/3`, `β ≤ 577/4500` beats `HD(1)`, and `β ≤ 1/18` gives `3/4`.

### F3. Riemann–Roch in the oscillatory regime

**Question.** Construct, from the actual source, a section count `h⁰` on the scaling surface with RR and Bézout on the same cone, and deduce `D < 2` (`D` is even, so `D = 0`).

**Why.** Weil's method is the only purity proof that needs neither a base (F1) nor beyond-threshold cancellation (F2). ACS shows that ingredients (i)–(iv) of Weil's proof are exact and that RR is missing.

**Requirements forced by §2.**
- (R1) `h⁰` cannot come from dominated payment, since the pole budget has no leverage on primitive classes. It must count sections whose positivity is oscillatory.
- (R2) It must be real-valued and non-additive under finite readings, since finite readings plus mass never give Bézout. The van der Geer–Schoof `h⁰ = log θ` is already such a regularized, oscillatory count.
- (R3) On the pole plane it must reduce to the theta `h⁰`, with its exact RR.
- (R4) Over `F_q` it must reduce to Weil's `h⁰` and fail RR on the golden datum.
- (R5) Its finite-dimensional shadow is the near-radical, with Landau–Widom count `(2∓η)e^{2L}`.

**Quantization.** The Weil route's integer is the Hodge defect, and the needed budget is `D < 2`. This is the analogue of the quantum budget, which multiplicative positivity cannot meet.

**A construction to try.** Indefinite theta series on finite-rank sublattices of Hecke cycles, using Vignéras' modularity criterion and Zwegers' completions. Their Poisson/RR identity holds exactly under a signature condition, and the scaling surface's signature condition (one positive square) is RH. An indefinite theta `h⁰` built from arithmetic and proved modular would therefore force the signature: Weil's "RR ⇒ Hodge" in theta form. No such construction appears in the corpus. First test: rank 3 (pole plane plus one Hecke cycle), then the golden datum.

### 3.4 Why these replace Q1–Q3

- **Q1, selection.** Beyond aperture `½ log Γ`, selection is F2 at a single height.
- **Q2, coupled positivity.** It now exists and is depth-homogeneous; the missing ingredient is F1's base.
- **Q3, escape through the paid ideal.** It cannot exclude escape, because the actual escape states are annihilated by the paid ideal automatically (§2.3).

## 4. Q3 — the new field: Arithmetic Künneth Theory (AKT)

### 4.1 The question

Over `F_q`, one fact drives both purity proofs: the zeta function of `X × Y` has spectrum the products of spectra, and its point counts `N_m(X)N_m(Y)` are positive. Weil uses `C × C`; Deligne uses fibre powers over a base. Over ℤ the product Spec ℤ × Spec ℤ is missing.

AKT asks: **what is Spec ℤ × Spec ℤ, as seen through its trace, and which positivity does it carry?**

### 4.2 Point of view

- Zeros are global spectra, and products of spectra are realized by near-coincidences of prime-power logarithms.
- The Nyquist scale of the logarithmic grid (spacing `e^{−x}` at height `x`) is the resolution at which the product becomes arithmetic: bounded additive shifts, i.e. Bézout pairs.
- Positivity on the product is free (`Λ ≥ 0`). The pole part (singular series) is a genuine arithmetic main term.
- Purity of the product is Hardy–Littlewood with square-root error. The field's bet is that the product has more structure than the factor: two projections, additive and multiplicative correspondences, Bézout intersection numbers, and configuration-space cohomology over `F_q[T]`.
- Every positivity is classified by how it pays negative spectral mass: dominated, oscillatory or shared. RH is the statement that one simple pole and the archimedean density pay every zero at the critical rate.

### 4.3 Objects

| Object | Definition | Function-field counterpart |
|---|---|---|
| Positive source | `Λ_F ≥ 0`, functional equation, pole order `κ`, trace `T_F` (explicit-formula distribution) | zeta of a variety |
| External powers | `T_F^{⊠k}` on `ℝ^k` | `H^*(X)^{⊗k}` |
| Nyquist square / k-fold product | renormalized diagonal of `T_F^{⊠k}` at resolution `e^{−x}`; point counts `Σ_n Π_j Λ(n+h_j)` | `N_m(X^k)`, or point counts of configuration varieties |
| Künneth defect | renormalized product minus the ideal spectral product | zero (Künneth) |
| Pole part per degree | singular series `𝔖(h)` and its k-tuple analogues | H⁰, H^{2k} |
| Correspondences | Hecke dilations `n ↦ pn`, successor `n ↦ n+h`, Bézout incidences `pa − qb = h` | Frobenius graphs, diagonal |
| Coefficient systems over a base | `F` on `B` with local traces and monodromy (F1) | lisse sheaves on a curve |
| Payment decomposition | dominated (finite rank, pole-paid), oscillatory, shared | — |
| Spectral modules | cofactor modules as spectral measures (§2.3); their tensor products | `H¹` as a Frobenius module |

### 4.4 Language

Weight, depth, amplification degree, Nyquist scale, near-coincidence, Künneth defect, pole part per degree, base, coefficient system, dominated, oscillatory and shared payment, Bézout correspondence, configuration trace, quantum budget, homogeneity class.

### 4.5 Foundational principles

1. **Product principle.** Every proof of purity applies positivity on a product object; a proof of RH must as well.
2. **Homogeneity principle.** An operation whose amplified trivial bound scales with its amplification produces no rate. The burden of a mechanism is to exhibit a non-scaling term: the base loss in Deligne, the genus in Weil.
3. **Bézout principle.** Over ℤ, products of spectra exist only through additive structure. A statement true for all Beurling systems is not an AKT statement.
4. **Payment principle.** Every positivity names its payment. Dominated payment is complete (budget, gauge collapse, `κ = 1` rigidity); the subject of the field is oscillatory payment.
5. **Construction before sign.** Product objects are built from the actual source with explicit renormalization. Their sign comes afterwards.
6. **Calibration principle.** Every theorem specializes over `F_q` (or `F_q[T]`) to a Künneth or configuration-space statement provable from Deligne. It must fail, for a stated reason, on Beurling systems, shifted pairs, the golden datum and the pole-order models.

### 4.6 Criteria the field must fulfil

- **C1.** Reproduce Weil (surface Hodge index) and Deligne (tensor-power estimate) over `F_q` inside the formalism. Reproduce Sawin–Shusterman's correlation asymptotics over `F_q[T]` as Künneth statements.
- **C2.** Recover the known ℤ results as low-degree or low-support cases: PNT and Vinogradov–Korobov in degree 1; Montgomery's pair correlation for `|α| < 1` and Goldston–Montgomery in degree 2; averaged Hardy–Littlewood in long shift ranges; Rudnick–Sarnak support.
- **C3.** Produce at least one unconditional statement beyond the square-root threshold with a *signed* error.
- **C4.** Pass the selectivity battery.
- **C5.** Every renormalization explicit, with no RH-equivalent hypothesis; formalizable in Lean.

### 4.7 Research programme

| Topic | First theorem to aim for |
|---|---|
| T1 Homogeneity no-gos | The amplification homogeneity law for twists, products, k-level forms, family averages and absolute tensor powers (A1). |
| T2 Nyquist renormalization | Existence of the renormalized square; counterterm; identification of the pole part with `𝔖(h)` (C1, C2). |
| T3 Künneth defect | Compute the defect for model systems. Show it vanishes over `F_q[T]` via configuration spaces. Name what replaces it over ℤ. |
| T4 Correspondence geometry | Intersection numbers of Hecke × successor cycles (Bézout counts); a Castelnuovo–Severi inequality for prime-weighted successor graphs. |
| T5 Bases and coefficient systems | The base axioms (F1) and the multiplicative no-go (A3). |
| T6 Payment theory | Canonical dominated/oscillatory decomposition of a positive source; a quantitative "oscillation discount" (minimal pole weight by domination versus 1 by oscillation). |
| T7 Spectral modules | Escape modules as spectral measures (B1–B4); tensor products of such modules. |
| T8 Near-coincidence geometry | Counting `|Σ ε_j log n_j| < η` with prime weights; Baker lower bounds as rigidity; sieve weights compatible with signs (F2). |
| T9 Theta sections | Indefinite theta `h⁰` on Hecke sublattices (F3); signature as modularity. |

### 4.8 Place of the existing programmes

- TTPC is AKT in degree 2 at bandwidth `λ > 1`.
- BiarithmeticGeometry is the correspondence algebra of the product at finite resolution.
- ACS and AOG are its multiplicative part (the scaling surface, Hecke cycles, orbit Hodge index).
- BVI and SSA supply the Bézout and successor correspondences.
- APD supplies positive Poisson pairs, which become rank-`k` pairs.
- MPG is degree-1 multiplicative payment, now complete.
- ADR is spectral modules (T7).

### 4.9 Retirement test

If T1 proves homogeneity for every product construction definable from the actual source, with no non-scaling term, then AKT reduces to F2 and should be absorbed into TTPC.

## 5. Targets

| Target | Kind | Programme |
|---|---|---|
| A1 Amplification homogeneity law | Lean (configurations) | SRT, AKT T1 |
| A2 Base axioms and `F_q` calibration | paper | ACS, AKT T5 |
| A3 Multiplicative no-go for bases | paper → Lean | APD, MPG |
| B1 Cofactor Gram = truncated translation Gram on the log line | Lean | ADR, BiarithmeticGeometry |
| B2 Admission ⇒ Plancherel spectral form | Lean | ADR |
| B3 Power-character kernels pass every ADR constraint | Lean | ADR |
| B4 Finite top ⇒ finite-rank escape limits | paper | ADR |
| C1 Nyquist renormalization of the trace square | paper | AKT T2 |
| C2 Smoothed Weil square = shifted prime correlations (finite) | Lean | TTPC, BVI |
| C3 Absolute-averaged power-saving Hardy–Littlewood ⇔ `Θ < 1` | paper → Lean | BVI, TTPC |
| D1 Retarget SSA open problem 1 (Tao settles it ineffectively) | card | SSA |
| E1 Brun–Titchmarsh constant below 2 by an auxiliary function | paper | BG, RHTower (Stepanov) |
| F2 narrow strip `β(δ) ≤ Bδ²/(1+δ)²` | paper | TTPC |
| F3 rank-3 indefinite theta `h⁰` with exact RR | paper | ACS, AOG |

## 6. Evidence

**Documents read in full.** `docs/reports/rh-current-frontier-map.md`; `docs/reports/rh-killed-routes.md`; `docs/reports/review-2510/{route-unification-ledger,hard-obstacles,walls-ledger,what-forces-blindness}.md`; the READMEs of `arithmetic-positivity-theory`, `BiScaleUncertainty`, `TransHorizonIncidenceMechanics`, `BezoutValuationIncidence`, `ArithmeticCriticalityTheory`, `SquareRootThreshold`, `ArithmeticIncidencePositivity`, `ArithmeticContinuationAndCriticalEnergy`, `ScaleSignedIncidenceCriticality`, `ArithmeticCompensationTheory`, `ArithmeticCastelnuovoSeveri`, `SignedArithmeticEnergyIncidence`, `TransThresholdPairCorrelation`, `ArithmeticOrientationTheory`, `ArithmeticOrientationGeometry`, `ArithmeticLocalDivisorGeometry`, `SignedSuccessorArithmetic`, `ArithmeticDefectRigidity`, `BiarithmeticGeometry`, `MultiplicativePositivityGeometry`, `ArithmeticPositiveDuality`. On the user's pointers: `docs/drafts/pipeline/2-fully-proven/strip-bochner-weil-pole-budget-forcing-law.md`, `StripBochnerWeilForcing/{StripBochnerShadows,InfiniteGaugePoleRigidity}.lean` (statements), `ArithmeticPositiveDuality/TheQuantumBudgetOfMultiplicativePositivity.lean`, `ArithmeticPositiveDuality/TheBlindIdealIsClosedOnlyWhereOffLineZerosAreSeen.lean` (headers).

**Corpus searches** (`scripts/formal_tools.py research`):

| Query | Result used |
|---|---|
| Fourier quasicrystal / crystalline measure | SRT crystal laws only |
| Lee–Yang polynomial / real stable / Kronecker line | `ZetaZerosLeeYangQuasicrystal`, `LeeYangRestrictionZeroCount`, `LeeYangPrimeStabilityNoGo`, `StableDirichletPolynomialPutnam` |
| tensor power trick / amplification / Deligne | `TensorPolarizationAmplification` (negative index), receiver amplification; no depth amplification |
| Stepanov / auxiliary polynomial | `RHTower/StepanovCount`, `HTGeometry/ShiftedSubgroupStepanov`, Baker auxiliary functions |
| sign uncertainty (BCK, Cohn–Gonçalves) | none |
| Fourier interpolation (Radchenko–Viazovska) | none |
| Hardy–Littlewood k-tuples ↔ n-level correlations | BVI tuple structure factor, `PairCorrelationFourThirds` |
| Deuring–Heilbronn | none |
| Rankin trick / symmetric power | `GenericUnitaryExponentBounds` (local archimedean only) |
| homotopy / collision deformation | winding and collision modules; no continuity method |
| Kurokawa tensor / Künneth of zero spectra | none |
| multiplicative chaos | `SteinhausModel` only |
| Turing method | none |
| convex cone of positive measures with FE | none |
| Connes–Consani archimedean positivity | `ConnesConsani*` operator modules |
| Lagarias–Rains two-variable zeta | none |
| Buium / Fermat quotient | none (killed-routes no-go-167 only) |
| Gonek symmetrized Euler product | `EulerExponentialCarrierCriticalLine` |
| Chowla / Tao / entropy decrement | `Sieve/AveragedChowlaInterface` (interface only); Matomäki–Teräväinen sieve modules |
| function-field twin primes (Sawin–Shusterman) | none |
| pronic step embedding | `finitePronicPairing_eq_stepGram` |
| indefinite theta (Vignéras, Zwegers) | none |
