# Regularization-freshness — zeta-regularization creates transcendence (G16)

- **ID:** regularization-freshness
- **Stage:** 1-in-progress (0→1 done 2026-06-19: "fresh" given a precise meaning; the Stieltjes seam
  identification proven; freshness reduced to the seam/F₁ — the transcendence itself stays open)
- **Type:** CANDIDATE → CONJECTURE (native), with a structural BRIDGE backbone
- **Priority:** FUTURE
- **Source:** ../../door/bucket-the-seam-archimedean-obstruction.md (#74 SEED-S), ../../door/bucket-new-sibling-conjectures.md · 00-status row #75
- **Statement:** Zeta-regularization / Hadamard finite-part is a **transcendence-CREATING** operation
  (`log 2π = −2ζ'(0)`; Glaisher `ζ'(−1)`). **Conjecture:** the regularization constants attached to a
  hypertranscendental object are transcendentally **fresh** relative to its periods — and this freshness
  is the field's **irreducible new transcendence.**

## Goal
Explains **structurally why the field is not a sub-case of period theory:** the Stieltjes constants and
the other regularization data are not periods of any motive — they are *manufactured* by the
regularization that the hypertranscendental `ζ` forces (no finite differential equation ⟹ regularization
is unavoidable). This feeds the Stieltjes side of DSS-cross (`g2-dss-lower-bound.md`) and the no-period
block of the secular weld (`tate-prime-rigidity.md`).

## Results (0→1, 2026-06-19, DeWitt)

### R1 — "fresh" given a precise meaning
A regularization constant `c` attached to `ζ` is **fresh** iff `c` is **algebraically independent of the
`MT(ℤ)` period algebra** `𝒫 = ℚ(2πi, {ζ(2k+1)}, MZVs)` (Brown: periods of `MT(ℤ)` = the MZV algebra). For the
Stieltjes block this is exactly **DSS-cross** (`g2-dss-lower-bound.md`): `{γ_n}` alg. independent of `𝒫`.
Freshness of the *whole* hypertranscendental class = the regularization map lands outside `𝒫̄`.

### R2 — the Stieltjes constants ARE the archimedean–arithmetic seam, as numbers (proven, structural)
By definition (Euler–Maclaurin), with `f(x) = (log x)^n/x`,
```
   γ_n = lim_{m→∞} [ Σ_{k=1}^{m} f(k) − ∫_1^m f(x) dx ],     ∫_1^m f = (log m)^{n+1}/(n+1).
```
The subtracted counterterm `∫_1^m (log x)^n/x dx` is **exactly the archimedean (continuous/integral) part**,
and the sum `Σ_{k≤m} (log k)^n/k` is the **arithmetic (discrete, prime-built) part** — since
`(log k)^n = (Σ_p v_p(k) log p)^n` is the all-integer version of the friable degree-`n` log-monomial form
(`../2-fully-proven/friable-dirichlet-auxiliary.md` §5). Therefore

> **`γ_n` = (arithmetic prime-side sum) − (archimedean integral) = the regularized discrete–continuous
> defect = the archimedean–arithmetic SEAM made into a number.**

This is the structural reason the `γ_n` sit on the **period/non-period divide**: the arithmetic side is
height-bearing log-monomials (escaping the §17.3 vacuum), the archimedean counterterm is the `F₁`, and `γ_n`
is their defect. Proven (it is the definition, re-read through the seam); grade **BRIDGE**.

### R3 — freshness ⟺ the seam/F₁ is non-trivial (the reduction)
The finite arithmetic forms (friable log-monomials) lie in `ℚ({log p})`; the archimedean counterterm is the
continuous integral. **Freshness** (`γ_n ∉ 𝒫̄`) holds iff the regularized defect is transcendentally
independent of `𝒫` — i.e. iff the **archimedean counterterm injects transcendence not already in the prime
log-monomials / the periods** = iff the **single missing Frobenius `F₁` (seam) is non-trivial** on the
Stieltjes data. So **G16-freshness ⟺ the seam is non-trivial ⟺ (via friable §5a) obstruction-C / Schanuel
for prime logs holds on the regularized limit.** This places G16 on the same `F₁` as G1, G2, G4 — now from
the *regularization* face.

### R4 — honest boundary on the toy instances
`log 2π = −2ζ'(0)` and Glaisher `ζ'(−1)` are the lowest-rung regularization constants. Whether they are
*fresh* (vs. lying in `𝒫̄` extended by `log p`) is a delicate **exponential-motive / Fresán–Jossen**
question I am **not** settling here — `log 2π` mixes `π` (a period) with `log 2` (an alternating-MZV period),
so it is plausibly *tame*, not fresh; freshness is expected only at the **higher rungs** (growing log-monomial
degree, the `γ_n`). [Motivic period-membership of these constants: flagged unverified, open — the conjecture's
content is the high-rung class, not the toy base.]

## Door passport
- **Door-1/4:** the freshness is a property of the **regularization forced by hypertranscendence** (the
  difference / infinite-base setting), not present in any holonomic parent.
- **Door-2:** "regularization creates fresh constants" uses classical transcendence tools to verify
  individual instances (BRIDGE for each `log 2π`-type fact); the **general principle** (freshness for the
  whole hypertranscendental class) is the native-candidate content.

## Gates
- [x] 0 → 1  in-progress: "fresh" given a precise meaning (R1: alg. independence from the `MT(ℤ)` period
  algebra = DSS-cross); the Stieltjes seam identification proven (R2: `γ_n` = discrete–continuous defect =
  archimedean–arithmetic seam); freshness reduced to the seam/F₁ (R3); toy instances honestly bounded (R4)
- [ ] 1 → 2  fully-proven: freshness proved for a concrete regularization constant vs the `MT(ℤ)` periods,
  then the general principle — **needs the transcendence input** (= DSS-cross / Schanuel for prime logs,
  Fields-Medal open; the R2 seam identification is the structural BRIDGE backbone, banked)
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Start with the proven facts `log 2π = −2ζ'(0)`, Glaisher `ζ'(−1)`, and ask their independence from the
`MT(ℤ)` period algebra; scale up to the Stieltjes `γ_n`. The right framework is exponential-motives /
Nori (Fresán–Jossen), where regularization constants are exponential periods.

## Cross-references
- `g2-dss-lower-bound.md` — the Stieltjes side of DSS-cross is regularization-fresh.
- `tate-prime-rigidity.md` — the non-period block of the secular weld is the fresh part.
- `is-lambda-a-period.md` — `Λ` may be another freshness instance.

## Log
- 2026-06-19 — created in 0-backlog. Regularization-freshness (G16, SEED-S): zeta-regularization is
  transcendence-creating — the field's irreducible new transcendence, distinct from period theory.
- 2026-06-19 (DeWitt) — moved 0→1. **R1** precise meaning (fresh = alg. indep. of `MT(ℤ)` periods =
  DSS-cross). **R2 (proven, BRIDGE):** `γ_n = lim_m[Σ_{k≤m}(log k)^n/k − (log m)^{n+1}/(n+1)]`, the
  counterterm `= ∫_1^m (log x)^n/x dx` is the archimedean integral, the sum is the arithmetic
  (prime-built log-monomial) part ⟹ **`γ_n` = the regularized discrete–continuous defect = the
  archimedean–arithmetic seam as a number.** **R3:** freshness ⟺ the counterterm injects transcendence
  beyond the prime log-monomials ⟺ seam/F₁ non-trivial ⟺ (friable §5a) Schanuel for prime logs on the
  regularized limit — same F₁ as G1/G2/G4. **R4:** toy instances (`log 2π`, Glaisher) honestly flagged as
  plausibly tame / period-membership unverified; freshness expected at higher rungs. Transcendence stays
  open (Professor's `baker-for-stieltjes`). No runpod used. Ledger note filed.
