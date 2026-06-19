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
complete regular (tame / classical-period) base** `𝓡 := 𝒫·ℚ({\log p})` — the compositum of the two
distinct regular subalgebras (Wheeler id=230):
- `𝒫 = ℚ(2πi, {ζ(2k+1)}, MZVs)` = periods of `MT(ℤ)` (Brown; **unramified** — contains `ζ(3)` but **not**
  `\log p`);
- `ℚ({\log p})` = Kummer periods of `MT(ℤ[1/N])` (**ramified** — contains `\log p` but **not** `ζ(3)`).

The earlier base `𝒫` alone was too narrow: #124 (Stieltjes–log no-isolation) shows `{γ_n}` cannot be
separated from `{\log p}`, so the base **must** include the Kummer column. The right base is therefore the
compositum `𝓡`, and freshness of the Stieltjes block is exactly the **DSS-cross relative apex**
(`g2-dss-lower-bound.md`, Wheeler §G/§H): `{γ_n}` algebraically independent **over `𝓡`**.

> **Tie to the wild kernel (`exponential-period-dss-cross`, DeWitt).** `𝓡` is precisely the **period field
> of `G_mot`** = the `K`-invariants `𝒪(P)^K` (`K = ker(G^exp ↠ G_mot)`). So **freshness over `𝓡` ⟺ `{γ_n}`
> are non-`K`-invariant ⟺ they are genuine `K`-coordinates** (the wild / exponential-motivic generators
> `J_m = ∂_s^m Σ_k Γ(s,k)|_{s=1}`, Professor). Regularization-freshness, the DSS-cross relative apex, and the
> `K`-nonconstancy are **one statement**: the tame base is `𝓡`; freshness **is** wildness.

Freshness of the *whole* hypertranscendental class = the regularization map lands outside `𝓡̄` (the wild
kernel acts nontrivially).

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
The finite arithmetic forms (friable log-monomials) lie in `ℚ({log p}) ⊂ 𝓡`; the archimedean counterterm is
the continuous integral. **Freshness** (`γ_n ∉ 𝓡̄`) holds iff the regularized defect is transcendentally
independent of the full regular base `𝓡 = 𝒫·ℚ({log p})` — i.e. iff the **archimedean counterterm injects
transcendence not already in the prime log-monomials AND the MZV periods** = iff the **single missing
Frobenius `F₁` (seam) is non-trivial** on the Stieltjes data. So **G16-freshness ⟺ the seam is non-trivial ⟺ (via friable §5a) obstruction-C / Schanuel
for prime logs holds on the regularized limit.** This places G16 on the same `F₁` as G1, G2, G4 — now from
the *regularization* face.

### R4 — honest boundary on the toy instances
`log 2π = −2ζ'(0)` and Glaisher `ζ'(−1)` are the lowest-rung regularization constants. Whether they are
*fresh* (vs. lying in `𝓡̄ = (𝒫·ℚ({log p}))̄`) is a delicate **exponential-motive / Fresán–Jossen**
question I am **not** settling here — `log 2π` mixes `π` (a period) with `log 2` (an alternating-MZV period),
both in `𝓡`, so it is plausibly *tame*, not fresh; freshness is expected only at the **higher rungs** (growing log-monomial
degree, the `γ_n`). [Motivic period-membership of these constants: flagged unverified, open — the conjecture's
content is the high-rung class, not the toy base.]

### R5 — the explicit auxiliary realization (Professor's `R_P`; DeWitt 2026-06-19, verified)
The R2 "regularized discrete–continuous defect" is realized by **one explicit native object**: Professor's
auxiliary `R_P(s) = Σ_j a_j Γ(s+j)ζ(s+j)` (chat id=250, `baker-for-stieltjes` §G), a finite ℤ-combination of
integer-shifted `Γζ` living in the `(σ_p,∂_s)`-module. Its pole-subtracted form `A_P = R_P − a_0/(s−1)` has
the **`a_0/(s−1)` counterterm = exactly the regularization counterterm of R2**. The `a_0` (unshifted, `j=0`)
part is the regularized `Γζ` jet `g(s)=Γ(s)ζ(s)−1/(s−1)`, whose `s=1` Taylor coefficients carry the **wild**
`γ_n` — verified `g(s)=0 + (−γ_1−½γ_0²+½ζ(2))(s−1)+…` (`computations/.../fe-stieltjes-triangular-dictionary.txt`,
ADDENDUM; ~12-digit numeric + exact Laurent/Taylor). The `j≥1` shifts give `Γ(1+j)ζ(1+j)=j!ζ(j+1)` = the
**tame** motivic block (Apéry `lcm(1..n)` arithmetic). So one object `R_P` realizes the `B_mot⊕B_wild` weld
(`tate-prime-rigidity`), the `K`-column (`exponential-period-dss-cross`), and the R2 regularization defect:
**"retention switch `a_0`" = "turn on the regularization counterterm" = "land in the wild kernel `K`."**

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
- `../5-failed/is-lambda-a-period.md` — **NOT** a freshness instance (withdrawn, DeWitt 2026-06-19):
  `Λ_dBN = 0 ⟺ RH` is tame/rational, not wild-fresh; the dBN no-margin is RH (localization axis), not a
  transcendence/period probe.

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
- 2026-06-19 (DeWitt) — **widened the freshness base** `𝒫 → 𝓡 = 𝒫·ℚ({log p})` per Wheeler id=230/§H:
  `𝒫` (MZV, unramified, no `log p`) and `ℚ({log p})` (Kummer, ramified, no `ζ(3)`) are distinct regular
  subalgebras; #124 no-isolation forces including the Kummer column, so the complete regular base is the
  compositum, and freshness = `{γ_n}` alg-indep **over `𝓡`** = the DSS-cross relative apex. Added the tie to
  `exponential-period-dss-cross`: `𝓡` = the period field of `G_mot` = `𝒪(P)^K`, so **freshness over `𝓡` ⟺
  `{γ_n}` non-`K`-invariant ⟺ wildness** — regularization-freshness, the relative apex, and `K`-nonconstancy
  are one statement. Updated R1/R3/R4 to base `𝓡`. No runpod, no web.
- 2026-06-19 (DeWitt) — added **R5**: R2's regularized defect is realized by Professor's explicit auxiliary
  `R_P=Σ_j a_j Γ(s+j)ζ(s+j)`; pole-subtraction `A_P=R_P−a_0/(s−1)` = the R2 counterterm; the `a_0`/`j=0` jet
  carries the wild `γ_n` (verified, `−γ_1−½γ_0²+½ζ(2)` at order 1), `j≥1` gives tame `j!ζ(j+1)`. Ties #75 to
  `baker-for-stieltjes`/`tate-prime-rigidity`/`exponential-period-dss-cross`. Local mpmath; archived.
- 2026-06-19 (DeWitt) — **rung-1 𝓡-freshness numerical evidence** (`../2-fully-proven/computations/2026-06-19-stieltjes-R-rung1-independence.txt`):
  PSLQ at dps=100/160/220 finds **no integer linear relation of height ≤1e6** among
  {1,γ₀,γ₁,γ₂,log2,log3,log5,ζ(2),ζ(3)} — i.e. {γ₀,γ₁,γ₂} are ℚ-linearly independent over the **correct joint
  base 𝓡=𝒫·ℚ({log p})** at rung 1 (R1). Evidence, not proof (PSLQ bounds height; linear only). Methodological
  catch (logged): a naive high-maxcoeff PSLQ returned a SPURIOUS relation (coeffs ~1e11, residual 8e-92 ≫ the
  1e-120 floor) — rejected by the residual-vs-floor + dps-stability check. RH-blind (transcendence side).
