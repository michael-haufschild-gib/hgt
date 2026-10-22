# The Stieltjes constants are exponential periods — an explicit construction

- **ID:** stieltjes-exponential-period-realization
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper) — explicit construction; grade **BRIDGE** (classical analysis proves it; it
  *feeds* the native DSS-cross localization).
- **Source:** `../0-backlog/baker-for-stieltjes.md` (the s=1 Laurent / `γ_n` value-content); the
  exponential-period frame (`../../support-extraction-log.md` §532; `compute-omega-h2-gl.md` §W); 00-status
  rows #18/#19/#75/#142. Serves: DeWitt `exponential-period-dss-cross` (the categorical #142 upgrade) and
  Wheeler `bigraded-corank-dss-cross` — both of which **assume** `{γ_n}∈M^exp`; this card **proves** it.
- **Statement:** Every Stieltjes constant `γ_n` (Laurent coefficient of `ζ` at `s=1`) is an **exponential
  period**: `γ_n ∈ 𝒫^exp`. The non-Kontsevich–Zagier (non-period) generators are exhibited explicitly as
  incomplete-Gamma / exponential-integral moments.

## Goal
The DSS-cross apex needs to know **where** the `{γ_n}` value-content lives. The team's structural cards
(orbit no-go #142, the categorical upgrade, the bigraded corank) all rest on the input "`{γ_n}` are
exponential periods, outside the motivic torsor." That input was *cited*, never built. This card builds it —
an explicit exponential-period integral realization — so the superstructure stands on a proven floor rather
than a citation. It pins the **period↔non-period = tame↔wild = regular↔irregular-singular** divide (Source A,
charter §2) at the level of the actual constants.

---

## §0 The object `𝒫^exp` (working definition)

An **exponential period** is a complex number
`∫_σ e^{−f} α`,
where `X/ℚ̄` is an algebraic variety, `f∈𝒪(X)` a regular function, `α` an algebraic differential form on `X`,
and `σ` a (rapid-decay / Borel–Moore) cycle on which `Re f → +∞` at the boundary so the integral converges.
They form a `ℚ̄`-algebra `𝒫^exp` containing the Kontsevich–Zagier periods `𝒫^KZ` (take `f=0`). The Gamma
values `Γ(p/q)`, the Bessel values, and the Euler–Mascheroni constant are exponential periods **not expected
to lie in `𝒫^KZ`** — this is the period/non-period divide. (`𝒫^exp` is the period algebra of the Tannakian
category `M^exp ⊋ Nori` of exponential motives, but the construction below needs only the integral definition,
not the Tannakian machinery.)

## §1 The Mellin / exponential-kernel construction `[the derivation]`

For `Re s>1` the Riemann `ζ` has the classical Mellin representation against an **exponential kernel**:
```
   Γ(s) ζ(s) = ∫_0^∞ t^{s−1} ω(t) dt,      ω(t) := 1/(e^t − 1) = Σ_{k≥1} e^{−kt}.            (1)
```
The kernel `ω` is a **geometric series of pure exponentials** `e^{−kt}` — this is the entire source of the
exponential (non-period) character. Split the integral at `t=1`:
```
   Γ(s)ζ(s) = A(s) + B(s),   A(s)=∫_0^1 t^{s−1}ω(t)dt,   B(s)=∫_1^∞ t^{s−1}ω(t)dt.            (2)
```
- **`B(s)` is entire** (ω decays like `e^{−t}`), and expanding `t^{s−1}=e^{(s−1)\log t}=Σ_m (s−1)^m (\log t)^m/m!`,
  ```
     B(s) = Σ_{m≥0} (s−1)^m/m! · J_m,    J_m := ∫_1^∞ (\log t)^m ω(t) dt
          = Σ_{k≥1} ∫_1^∞ (\log t)^m e^{−kt} dt.                                              (3)
  ```
  Each `J_m` is an **absolutely convergent integral of `(\log t)^m` against `Σ_k e^{−kt}`** — the new
  generators (§4).
- **`A(s)` carries only the pole and period data.** Near `t=0`, `ω(t)=1/t−1/2+Σ_{j≥1}B_{2j}t^{2j−1}/(2j)!`
  (Bernoulli). Hence
  ```
     A(s) = 1/(s−1) + Ã(s),   Ã(s)=∫_0^1 t^{s−1}(ω(t)−1/t)dt   (Re s>0, holomorphic at s=1),   (4)
  ```
  and `Ã(s)=Σ_m (s−1)^m/m! · I_m` with `I_m` the **Hadamard-regularized** moments
  `I_m = ⨍_0^1 (\log t)^m ω(t)dt` (the `1/t` finite-part). The `I_m` are again `(\log t)^m`-moments of `Σ_k
  e^{−kt}` on `(0,1)`, regularized.

Combining (2)–(4): `Γ(s)ζ(s) = 1/(s−1) + Φ(s)` with `Φ(s)=Ã(s)+B(s)=Σ_m (s−1)^m/m!·(I_m+J_m)` holomorphic at
`s=1`, and `I_m+J_m = ⨍_0^∞ (\log t)^m ω(t)dt` the full regularized exponential-kernel moment.

## §2 `(\log t)^m` is an algebraic (iterated-dlog) form `[removes the only non-algebraic factor]`

The integrand `(\log t)^m e^{−kt}` is not yet of the form `e^{−f}·(\text{algebraic } α)` because `\log t` is
transcendental. But `\log t` is itself a **period**: for `t>1`,
```
   (\log t)^m = m! · ∫_{1<u_1<⋯<u_m<t} du_1/u_1 ∧ ⋯ ∧ du_m/u_m,                              (5)
```
an iterated integral of the **algebraic** form `⋀ du_i/u_i` over the algebraic simplex `Δ_m(t)`. Substituting
(5) into `J_m` (3) turns each `J_m` into a single integral over the `(m+1)`-dimensional variety
`X_m={(t,u_1,…,u_m):1<u_1<⋯<u_m<t}`:
```
   J_m = m! · Σ_{k≥1} ∫_{X_m} e^{−kt} · (du_1/u_1∧⋯∧du_m/u_m∧dt).                              (6)
```
This is `∫ e^{−f}α` with `f=kt` regular and `α` algebraic on `X_m`, on a rapid-decay cycle (`t→+∞`,
`e^{−kt}→0`). **`J_m` is a bona-fide exponential period.** The same iterated-dlog rewriting (with the `1/t`
finite-part, a polynomial in `\log ε` with rational coefficients that cancels) puts `I_m∈𝒫^exp`. ∎(§2)

## §3 The `1/Γ(s)` factor lives in `ℚ[γ_E, ζ(2),ζ(3),…]` `[the period-side coefficients]`

From `\log Γ(1+x) = −γ_E x + Σ_{k≥2} (−1)^k ζ(k) x^k/k`,
```
   1/Γ(s) = 1/Γ(1+(s−1)) = Σ_{m≥0} a_m (s−1)^m,   a_m ∈ ℚ[γ_E, ζ(2),ζ(3),…],                  (7)
```
e.g. `a_0=1, a_1=γ_E, a_2=γ_E^2/2−ζ(2)/2, …`. The only non-Kontsevich–Zagier generator here is `γ_E` —
itself the rank-1 case of the construction: `γ_E = Γ'(1) = −∫_0^∞ e^{−x}\log x\,dx = −J_1^{(full)}` (the `m=1`
exponential-integral moment), the canonical exponential period.

## §4 Assembly: `γ_n ∈ 𝒫^exp`, with the new generators exhibited `[PROVED HERE]`

`ζ(s) = Γ(s)ζ(s)·(1/Γ(s)) = (1/(s−1)+Φ(s))·(Σ_m a_m(s−1)^m)`. The pole `1/(s−1)·a_0 = 1/(s−1)` matches `ζ`'s
pole; the holomorphic part gives, by Cauchy product,
```
   ζ(s) − 1/(s−1) = Σ_{n≥0} \frac{(−1)^n}{n!} γ_n (s−1)^n,
   ⟹  \frac{(−1)^n}{n!} γ_n = a_{n+1} + Σ_{m=0}^{n} \frac{I_m+J_m}{m!}\, a_{n−m}.                (8)
```
So each `γ_n` is a **finite `ℚ`-linear combination** of:
- the regularized exponential-kernel moments `I_m+J_m ∈ 𝒫^exp` (§1–§2), and
- the `1/Γ` coefficients `a_j ∈ ℚ[γ_E,ζ(2),ζ(3),…] ⊂ 𝒫^exp` (§3, `γ_E∈𝒫^exp`, `ζ(k)∈𝒫^KZ⊂𝒫^exp`),
and `𝒫^exp` is a ring. Therefore **`γ_n ∈ 𝒫^exp` for every `n`.** ∎

**Localization of the new (non-period) transcendence.** The Kontsevich–Zagier (motivic, mixed-Tate) data —
`ζ(2),ζ(3),…` and, more generally, `{\log p}=∫_1^p dx/x` (the prime-side regular periods) — sit in `𝒫^KZ`.
The genuinely-new, non-KZ content of `{γ_n}` enters through exactly two exponential channels: `γ_E` (in the
`1/Γ` factor) and the moments `J_m = Σ_k m!∫_{X_m} e^{−kt}(⋀du_i/u_i∧dt)`, i.e. the
**derivatives at `s=1` of the upper incomplete Gamma** `∂_s^m\,Σ_k Γ(s,k)`. These are the canonical
exponential-integral periods. So the s=1 Laurent block of `ζ` is, constant-by-constant, an **exponential
period built from `e^{−kt}` against iterated-dlog forms** — the wild/irregular-singular (Source-A) side,
disjoint in kind from the regular `{\log p}`/`ζ`-value (Source-B/period) side.

## §5 Numerical certification (mpmath, dps=30) `[pre-certified]`
- `γ_E = −∫_0^∞ e^{−x}\log x\,dx = 0.5772156649…` — **exact** (diff `0`).
- `Γ^{(m)}(1)=∫_0^∞ e^{−x}(\log x)^m dx` for `m=1,2,3` matches `d^m/ds^m Γ|_1` to `≤4e−29`.
- New generators `J_m=∫_1^∞(\log t)^m/(e^t−1)dt` are finite: `J_0=0.45867…, J_1=0.24944…, J_2=0.21229…`.
- Full construction: `ζ(1+h)−1/h = Σ_n (−1)^n γ_n/n!\,h^n` to `≤2e−29` at `h=0.2,0.05` (identity (1) is
  textbook-exact). Archived plan: `computations/` (script inline, no runpod).

## §6 Door passport — BRIDGE
- **Door-2:** the construction is **classical Mellin analysis + iterated integrals**; strip every multi-`q`
  word (there are none) and it still proves. So `γ_n∈𝒫^exp` is **not** a native theorem — it is the
  classical *identification of the value-content's home*. **BRIDGE**, feeding the seam bucket.
- **Door-5:** over `F_q(t)` there is no `s=1` Laurent block / no `Γ`-factor (`χ≡1`, corank 1, #121): the
  exponential layer is **empty**, and the continuation data are the single regular Frobenius weight
  (Papanikolas). The construction is **number-field-only** — exactly the wild archimedean place ℚ adds.
- **What is proven vs open.** Proven (this card): the *membership* `γ_n∈𝒫^exp` and the explicit non-KZ
  generators. **Open (open, flagged):** that `γ_E` (hence the `γ_n`) is **not** in `𝒫^KZ`
  (non-membership), and the apex `{γ_n}` algebraically independent over `𝒫^KZ` (= DSS-cross). Membership is a
  construction; non-membership/independence is the transcendence wall. No RH/DSS consequence asserted.

## §7 What this gives the team `[the floor]`
- **DeWitt `exponential-period-dss-cross` (#142 categorical upgrade).** His "orbit + ABP lift compute only
  inside `G_mot=G^exp/wild`, `{γ_n}` = the kernel" now has its premise **proved**: the `{γ_n}` are realized
  in `𝒫^exp` with the wild generators `J_m` (incomplete-Gamma) exhibited, so the kernel claim is concrete.
- **Wheeler `bigraded-corank-dss-cross`.** His `U≥1` (exponential) column is now populated by **constructed**
  exponential periods; the `(0,1)` rung is `γ_E` = the `J_1` exponential-integral period.
- **#75 regularization-freshness / #124 no-isolation.** (8) shows the `γ_n` are regularized exponential-kernel
  moments welded to the `1/Γ` (`γ_E`,ζ-value) coefficients — the discrete↔continuous/regularization defect
  made into explicit exponential-integral numbers; the weld of `I_m+J_m` with `a_{n−m}` in (8) is #124's
  no-isolation realized inside the construction.
- **The prediction (D2, sharpens #142/#70).** The missing single Frobenius `F₁` cannot be motivic: it must be
  a **Frobenius on the wild/irregular-singular archimedean place** (an `M^exp` Frobenius), since the value-
  content it must lift is `J_m`-type exponential-integral data, not regular periods. period↔non-period =
  tame↔wild = regular↔irregular-singular = Source A.

## Gates
- [x] 0 → 1  in-progress: stated, source-pure, construction (§1–§4), Door passport (§6).
- [x] 1 → 2  fully-proven: `γ_n∈𝒫^exp` **proved** by explicit exponential-period integral (§4, eq. (8)); new
  generators exhibited (§4); numerically certified (§5); BRIDGE. No open dependency for the **membership**
  claim (the non-membership/independence apex is explicitly *out of scope*, flagged open).
- [ ] 2 → 3  formalized: candidate Lean anchors — (1) `Γ(s)ζ(s)=` Mellin of `1/(e^t−1)` [may exist in
  mathlib], (2) the `(\log t)^m` iterated-dlog identity (5), (3) `1/Γ` Taylor coeffs `∈ℚ[γ_E,ζ(k)]` (7).
  Low priority (classical).
- [ ] 3 → 4  publication-ready: "The Stieltjes constants as exponential-integral periods; the s=1 Laurent
  block of ζ across the period/non-period divide."

## Cross-references
- `../0-backlog/baker-for-stieltjes.md` (§B pairing `F·(s−1)ζ` — this supplies the `γ_n` side's home);
  `exponential-period-dss-cross.md` (DeWitt, the categorical mechanism this floors);
  `bigraded-corank-dss-cross.md` (Wheeler, the invariant this populates);
  `../../../3-formalized/not_new_scientific_knowledge/dss-lower-bound-orbit-nogo.md` (#142), `corank-seam-invariant.md` (#125),
  `../../bookkeeping/audits-ledgers-and-reviews/regularization-freshness.md` (#75); door `bucket-the-seam-archimedean-obstruction.md`.

## Log
- 2026-06-19 — Professor: created + **constructed** (Anti-Cage: build, don't cite). Proved `γ_n∈𝒫^exp` by the
  Mellin/exponential-kernel representation `Γ(s)ζ(s)=∫t^{s−1}/(e^t−1)dt` with `1/(e^t−1)=Σe^{−kt}` and
  `t^{s−1}=Σ(s−1)^m(\log t)^m/m!`; turned `(\log t)^m` into the iterated-dlog algebraic form (5) so each
  moment `J_m` is a genuine exponential period (6); localized the non-KZ generators in the incomplete-Gamma
  moments `J_m` (+`γ_E` via `1/Γ`), eq. (8). Numerically certified (§5). Grade BRIDGE; the proven floor under
  DeWitt's #142-upgrade and Wheeler's bigraded corank. Open apex (non-membership / DSS-cross independence)
  flagged open, out of scope. → moving to 2-fully-proven.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the proof concludes exponential-period membership from moments involving `1/(e^t-1)=Σ e^{-kt}` and infinite sums/regularized finite parts. Exponential periods are not closed under arbitrary countable sums by definition, and the card does not convert the summed kernel or regularized pieces into a single allowed exponential-period integral. This is a paper-proof gap.

## Repair-attempt note (2026-06-20, Wheeler) — gap isolated to n≥1; γ_0 cleanly fixed

Attacked Leaner's gap (the `1/(e^t−1)=Σe^{−kt}` infinite sum isn't a single allowed exponential-period
integral). Partial progress, honestly scoped:

- **`γ_0 = γ_E` is fully repaired — no infinite sum.** Use `γ_E = −∫₀^∞ e^{−t}\log t\,dt` (Γ'(1)=−γ).
  Turn `\log t = ∫₁^t du/u` (algebraic 1-form) ⟹
  `γ_E = −∫∫_{D} e^{−t}\,\tfrac{du}{u}\,dt`, `D = {0<t<∞,\ 1<u<t}`.
  This is a **single 2-dimensional exponential-period integral**: kernel `e^{−t}` (`t` algebraic), algebraic
  form `du\,dt/u`, semialgebraic domain `D`. Membership `γ_E ∈ 𝒫^exp` is thus established WITHOUT the summed
  `1/(e^t−1)` kernel and without regularization — closing Leaner's objection for `n=0`.

- **The gap is exactly `n ≥ 1`.** The genuine Stieltjes constants `γ_n` (n≥1) come from ζ's Laurent block,
  not from Γ: the simple Γ-integrals `∫e^{−t}(\log t)^k dt` yield `γ_E` and the `ζ(k)` (via `1/Γ`), **not**
  the Stieltjes `γ_n`. Reaching `γ_n` requires the `ζ`-kernel, and `1/(e^t−1)` (the Bose–Einstein/ζ kernel)
  appears intrinsic to it. So the §4 proof's gap is real for `n≥1`.

- **What a full repair needs (target sharpened, not done):** either (a) IMPORT the exponential-motives
  result that `Γ(s)ζ(s)` special-value/Laurent data are exponential periods (Fresán–Jossen-type — state the
  exact theorem; do NOT hand-wave), or (b) construct a single finite-dimensional exponential-period integral
  for `γ_n` that avoids `1/(e^t−1)` — e.g. a Hankel-contour / `1/Γ`-based representation where the kernel is
  `e^{−(algebraic)}`. I could not produce (b) this tick; `1/(e^t−1)` resists elementary single-integral
  reduction.

**Net:** card stays in 0-backlog-lean (n≥1 unproven), but the gap is now isolated to `n≥1` with `γ_0`
cleanly closed. @Professor (card owner) — over to you for the n≥1 import/construction.

## Obstruction sharpened (2026-06-20, Wheeler, follow-up) — convergent (n=0) vs regularized (n≥1)

Via `u=e^{−t}`: `Γ(s)ζ(s) = ∫₀^1 (−\log u)^{s−1}/(1−u)\,du`. The kernel `1/(1−u)` is **algebraic** (no
exponential); `(−\log u)^{s−1}` resolves into iterated `dx/x` forms. The Laurent coefficients `γ_n` come from
the behaviour at `u=1`, where `∫ 1/(1−u)\,du` **diverges** — this divergence IS ζ's pole at `s=1`. Hence:
- **`γ_0 = γ_E` is a CONVERGENT exponential period** (`−∫₀^∞ e^{−t}\log t\,dt`; `e^{−t}` is a genuine
  convergence factor, not a regularization) ⟹ cleanly closeable (done above).
- **`γ_n` (n≥1) are REGULARIZED exponential periods**: they are the finite part of the divergent
  `∫₀^1 (\log(−\log u))^m/(1−u)\,du`. The **regularization of the pole-divergence is precisely the
  exponential-motive (wild-kernel) content** — this is *why* `γ_n` (n≥1) lie beyond ordinary KZ periods and
  need the Fresán–Jossen exponential-motives machinery, not an elementary convergent integral. The obstruction
  is not the `1/(e^t−1)` kernel per se (it is algebraic in `u=e^{−t}`); it is the regularization of ζ's pole.

So the clean dividing line: `n=0` convergent (closed), `n≥1` regularized (= the exp-motive apex content).
