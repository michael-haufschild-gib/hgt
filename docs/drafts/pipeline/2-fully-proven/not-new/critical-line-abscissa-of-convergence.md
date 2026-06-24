# Re = ½ is the abscissa of almost-sure convergence of the random Euler product

- **ID:** critical-line-abscissa-of-convergence
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) — Door-2 grade **BRIDGE**; **review fixes applied 2026-06-19** (½ normalization + divergence direction), ready for Lean
- **Priority:** FUTURE
- **Source:** split from `../1-in-progress/erosion-threshold.md` (G19); ../../door/bucket-time-and-non-holonomic-time.md · 00-status rows #59, #110
- **Statement:** On the boundary torus `𝕋^∞` (Bohr model: `X_p = e(θ_p)` i.i.d. uniform on the unit
  circle, one per prime), the random Euler observable
  `𝓛(σ) = Σ_p Σ_{k≥1} X_p^k p^{-kσ}/k = −Σ_p log(1 − X_p p^{-σ})`
  **converges almost surely iff `σ > ½`.** Equivalently `Re = ½` is the abscissa of a.s. convergence of
  the random Euler product `∏_p (1 − X_p p^{-σ})^{-1}`. The **total second moment**
  `V(σ) = Σ_p Σ_k p^{-2kσ}/k² = Σ_p E|ℓ_p|²` is finite for `σ > ½`, infinite for `σ ≤ ½`, and blows up
  like `log(1/(2σ−1))` as `σ → ½⁺` (truncation at `σ = ½`: `~ log log X`) — **no factor `½`**. The
  **real-part** variance is exactly half, `Var(Re 𝓛) = ½ V(σ) ~ ½ log(1/(2σ−1))` (truncation
  `~ ½ log log X`); since `Re 𝓛 = log|·|`, this is the half-normalized quantity matching **Selberg's CLT**
  for `log|ζ(½+it)|`.

## Proof

Write `t_p = X_p p^{-σ}` and `𝓛(σ) = Σ_p ℓ_p`, `ℓ_p = −log(1 − t_p) = Σ_{k≥1} X_p^k p^{-kσ}/k`. The
`{ℓ_p}` are independent across `p`.

**Mean and variance.** `E[X_p^k] = 0` for every `k ≥ 1`, so `E[ℓ_p] = 0`. The powers `{X_p^k}_{k≥1}`
are orthonormal (`E[X_p^k \overline{X_p^j}] = δ_{kj}`), hence
`E|ℓ_p|² = Σ_{k≥1} p^{-2kσ}/k²`, and
`V(σ) := Σ_p E|ℓ_p|² = Σ_p Σ_{k≥1} p^{-2kσ}/k²`. Splitting into real/imaginary parts,
`E[(Re ℓ_p)²] = ½ Σ_{k≥1} p^{-2kσ}/k² = ½ E|ℓ_p|²` **exactly** (because
`E[cos(2πkθ)cos(2πjθ)] = ½δ_{kj}`), and likewise for `Im`; hence `Var(Re 𝓛) = Var(Im 𝓛) = ½ V(σ)`. The
factor `½` is the real-part bookkeeping, not part of `V`.

**The threshold is the `k = 1` term.** `Σ_p Σ_{k≥2} p^{-2kσ}/k² ≤ Σ_p p^{-4σ}/(1 − p^{-2σ}) < ∞` for
`σ > ¼`, so the `k ≥ 2` tail never affects the transition near `σ = ½`. Thus for `σ > ¼`,
`V(σ) < ∞ ⟺ Σ_p p^{-2σ} < ∞`. Both directions of the prime-sum threshold:
**(convergence, `σ>½`)** `Σ_p p^{-2σ} ≤ ζ(2σ) < ∞` for `2σ > 1`; **(divergence, `σ≤½`)** for `2σ ≤ 1`
one has `p^{-2σ} ≥ p^{-1}`, so `Σ_p p^{-2σ} ≥ Σ_p p^{-1} = ∞` (Mertens). Hence
`Σ_p p^{-2σ} < ∞ ⟺ σ > ½`. (The `ζ(2σ)` comparison alone bounds only from above — it gives the
convergence half; the divergence half needs the Mertens lower bound, not the `ζ`-upper bound.)

**A.s. convergence.** The `ℓ_p` are independent, mean zero, and uniformly small (`|t_p| = p^{-σ} → 0`,
`|ℓ_p| ≤ 2p^{-σ}` for `p` large). For such terms the Kolmogorov three-series theorem reduces to the
single series `Σ_p E|ℓ_p|²`: the series `Σ_p ℓ_p` converges a.s. iff `Σ_p E|ℓ_p|² < ∞`. Combining with
the previous paragraph, `𝓛(σ)` converges a.s. `⟺ σ > ½`. For `σ ≤ ½` the variance diverges and the
series diverges a.s. ∎

**Blow-up rate.** With the prime zeta `P(s) = Σ_p p^{-s} = Σ_{k≥1} (μ(k)/k) log ζ(ks)`, near `s = 1`
one has `P(s) = log(1/(s−1)) + O(1)`. Hence `V(σ) = P(2σ) + O(1) = log(1/(2σ−1)) + O(1)` as
`σ → ½⁺` (**no `½`** — `V` is the total second moment), and the real-part variance is exactly half,
`Var(Re 𝓛) = ½ V(σ) = ½ log(1/(2σ−1)) + O(1)`. At `σ = ½`, Mertens gives
`Σ_{p ≤ X} p^{-1} = log log X + M + o(1)`, so the truncated variance of `log|ζ(½ + it)|` is
	  `~ ½ log log X`. The matching limit law on the line is **Selberg's central limit theorem**:
	  `log|ζ(½ + it)| / √(½ log log T) ⇒ N(0,1)` for `t ∈ [T, 2T]`.

## Lean-formalizer review note (2026-06-19) — RESOLVED

Both flagged issues fixed (researcher pass, 2026-06-19); numerically certified in
`../../../../computations/2026-06-19-abscissa-normalization-check.txt`.
1. **Normalization (`½`).** Kept the displayed `V(σ)=Σ_pΣ_k p^{-2kσ}/k²` (total second moment) and
   **removed the `½`** from its asymptotics: `V ~ log(1/(2σ−1))`, truncation `~ log log X`. Introduced the
   real-part variance `Var(Re 𝓛) = ½ V(σ)` — exact, via `E[cos(2πkθ)cos(2πjθ)] = ½δ_{kj}` — so the
   `½ log(1/(2σ−1))` / `½ log log X` / Selberg match now sits with `Re 𝓛 = log|·|`, where it belongs.
   *(Cert A: `P(2σ)` tracks `log(1/(2σ−1))`, offset → const ≈ −0.315, not `½·log`. Cert B: real/total
   ratio = 0.500000.)*
2. **Divergence direction.** The threshold paragraph now proves both halves: `≤ ζ(2σ)` for convergence
   (`σ>½`); `p^{-2σ} ≥ p^{-1}` ⟹ `Σ_p p^{-2σ} ≥ Σ_p p^{-1} = ∞` (Mertens) for divergence (`σ≤½`). *(Cert
   C.)* The `ζ(2σ)` comparison alone gives only the convergence half.

The threshold and a.s.-convergence dichotomy (`σ>½`) were never in doubt — the bug was only in the
blow-up *constant* of the displayed `V`. Statement and proof are now internally consistent.

**Dependencies (all classical):** Kolmogorov three-series theorem; Mertens' second theorem; the
Euler-product / prime-zeta expansion of `log ζ`; Selberg's CLT. *Attributions recalled, not re-verified
this session:* the abscissa-`½` statement is Wintner (1944) / Bohr–Jessen for the random multiplicative
model.

## Door-2 grade: BRIDGE
Stripped of the field's vocabulary, statement and proof are classical probabilistic value-distribution
theory on `𝕋^∞` (Wintner / Bohr–Jessen / Selberg). A parent (analytic number theory + probability)
proves it, so it is **BRIDGE**, not native C5. Its worth is a clean, **source-pure** characterization
of `Re = ½`: built only from the primes (`Σ_p p^{-2σ}`, Mertens), never from the zeros — and it does
not assume RH.

## Significance
`Re = ½` gets an intrinsic meaning independent of where the zeros are: it is the **unique vertical line
on which the Euler observable's variance is marginally (logarithmically) divergent** — the boundary
between a.s. convergence (`σ > ½`) and divergence (`σ ≤ ½`) of the random Euler product. This is the
rigorous backbone under the native conjecture **G19** (the dynamical erosion/Lyapunov dichotomy and the
"zeros = degenerations of the marginal cocycle" claim), which stays open in
`../1-in-progress/erosion-threshold.md`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (above; dependencies discharged by classical citation)
- [ ] 2 → 3  formalized — **pre-certified ✓**
  (`../../../../computations/2026-06-19-abscissa-normalization-check.txt`: the `loglog`-vs-finite split,
  the exact `½` real-part ratio, and the Mertens divergence). Lean: the elementary core
  "`Σ_p p^{-2σ} < ∞ ⟺ σ > ½`" is Tier-A (`≤ ζ(2σ)` above ½; `≥ Σ_p 1/p` Mertens below); the blow-up
  constants and Selberg's CLT are classical imports, **not** Lean-bound.
- [ ] 3 → 4  publication-ready

## Log
- 2026-06-19 — created in 2-fully-proven, split from `erosion-threshold` (G19); backbone proof, Door-2 grade BRIDGE.
- 2026-06-19 — returned by Lean review to `0-backlog-lean` (½ normalization mismatch + divergence-direction gap).
- 2026-06-19 — **review fixes applied** (researcher pass): (1) `½` normalization — `V` kept as the total
  second moment with `V ~ log(1/(2σ−1))`; the `½` moved to `Var(Re 𝓛) = ½V` (exact); (2) divergence
  direction made explicit via Mertens (`p^{-2σ} ≥ p^{-1}`). Numerically certified
  (`computations/2026-06-19-abscissa-normalization-check.txt`). Review note marked **RESOLVED**; Type →
  THEOREM (paper), **ready for Lean**. Kept in `0-backlog-lean` (the Lean queue).
- 2026-06-19 (Leaner) — folder correction: card declares `Stage: 0-backlog-lean` and its own log says it was kept in the Lean queue after review fixes, so moved from `2-fully-proven` to `0-backlog-lean`. Not a new mathematical rejection in this pass.

## Verification + re-bank — 2026-06-19 (Professor)
Independently verified all quantitative claims before re-banking (the 0-backlog-lean move was a folder/metadata
correction, not a mathematical rejection — Leaner's own note, line 109):
- **Threshold** `V(σ)<∞ ⟺ σ>½`: rigorous (Kolmogorov three-series reduces to `Σ_p E|ℓ_p|²`; `k≥2` tail
  bounded — numerically `0.112` at σ=0.55, finite for σ>¼; `Σ_p p^{-2σ} < ∞ ⟺ σ>½` via `ζ(2σ)` upper +
  Mertens `p^{-2σ}≥p^{-1}` lower). Mertens confirmed: `Σ_{p≤X}1/p` matches `loglogX+M` to 3 digits.
- **Blow-up** `V(σ)=P(2σ)+O(1)~log(1/(2σ−1))`: verified via `P(2σ)=Σ_k μ(k)/k·log ζ(kσ·2)` (prime
  TRUNCATION cannot reach this — needs primes to `~e^{1/(2σ−1)}`); `P(2σ)−log(1/(2σ−1)) → −0.3157` (constant,
  Mertens-related), matching the card's `≈−0.315`. `computations/2026-06-19-abscissa-blowup-verify.py`.
- **Real-part ratio** `Var(Re𝓛)/V = ½` exact (`E[cos²]=½`, analytic).
Proof rigorous and internally consistent; dependencies classical (Kolmogorov three-series, Mertens,
prime-zeta/log ζ, Selberg CLT — all credited IMPORTs). Door-2 **BRIDGE**. → **2-fully-proven**.
