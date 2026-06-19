# Bucket G5 — Unitarity gatekeeper (candidate)

**Bucket grade:** organizational (SEARCH channel). Sorted from `docs/support-extraction-log.md`. The
**single richest bucket** — RH appears in ~7 concrete, mutually-reinforcing unitarity/positivity
forms, several with axiom-clean Lean footholds.
**Scope (one line).** The non-integrable multi-q connection has **unitary holonomy on the σ-fixed
locus ⟺ spectrum real ⟺ RH.** This is the bridge that would unify "time" (A2) with "RH-byproduct"
(A1).
**Work package this seeds.** State candidate G5 **in carrier form** — `RH ⟺ m_ξ = −Ξ′/Ξ is Herglotz
(κ₋=0) on ℂ⁺` — and pursue the **one archimedean rigidity bound** (the multiplicity estimate on `G_L`)
that would force it; the multiplicative side is already fully diagonalized.

---

## The conjecture

> **G5 (candidate) — Unitarity gatekeeper:** a non-integrable multi-q connection has unitary holonomy
> on the σ-fixed locus ⟺ its spectrum is real ⟺ RH.

The σ-fixed locus is **the critical line** (the native home, below). Candidate G5 has ~7 equivalent
faces; they are all "the σ-fixed locus carries a norm-preserving (self-adjoint generator) structure."

---

## The native home — the σ-fixed locus is the critical line (#67)
- **Lemma 1 (a real computation, not conjecture):** the FE `σ:s↦1−s` acts on every prime coordinate at
  once as inversion-and-scale `x_p ↦ p^{−1}x_p^{−1}`; its **fixed-*modulus* locus is exactly the
  critical line** `|x_p|=p^{−1/2} ∀p ⟺ Re s=½`. So **RH = "every zero lies on the σ-fixed-modulus
  locus of the infinite-base difference system."** *Air: Lemma 1 verified; the localization is RH.*
  (ledger: `BoundaryModulus`, `sigmaConj_fixed_iff_critical`, `ArakelovW`)
- §10-Critic: the draft already poses G5 nearly verbatim — *"is the boundary action of `σ⋉𝕋^∞`
  **unitarizable** on the Nyman–Beurling space?"* / *"does the σ-inversion make the boundary dilation
  generator self-adjoint in the `H²(𝕋^∞)` metric?"*

---

## The ~7 faces (all RH, all the same gatekeeper)

### Face 1 — the carrier germ is Herglotz (#76 — THE A1/A2 unification anchor)
- The carrier `m_ξ(z) = −Ξ′/Ξ(z) = Σ_ρ 1/(ρ−z) = Σ_{k≥0} P_{k+1} z^k`. **A1 (RH) = the germ's GLOBAL
  analytic type:** `m_ξ` Herglotz ⟺ `κ₋=0` ⟺ no ℂ⁺-poles ⟺ RH. **A2 (DSS) = the germ's INFINITE JET
  at 0:** `{P_k}` algebraically independent. *Candidate G5 in carrier form: `m_ξ` Herglotz/unitary ⟺
  RH.* (the full unification → [[bucket-A1-A2-unification-the-carrier]])
- Finite anchor **ledger-proven:** `multiPair_carrier_exact_neg_inertia` — `κ₋ = #off-line conjugate
  pairs` *exactly*, via explicit Krein–Langer factorization + Cauchy non-degeneracy. RH = the `k=0`
  limit. Open: the infinite passage (Krein–Langer `N_κ` + Nevanlinna/Pick at infinite nodes,
  regularized Hadamard — mathlib gap, `MeasureCarrier`/`CarrierPickKernel`/`CayleySchur` are the start).

### Face 2 — uniform secular total positivity, `Λ=0` (#77)
- §1–2 two determinantal faces on `c_n=ξ(½)e_n({1/γ²})`: **Hankel** (Hermite, `κ₋` = #negative
  eigenvalues = #off-line σ-quadruples — `secular_hankel_signature`) and **Toeplitz** (Pólya-frequency
  / total positivity). RH ⟺ both. §5–6: **RH ⟺ secular Toeplitz totally positive to ALL orders ⟺
  Ξ∈Laguerre–Pólya ⟺ `Λ≤0`** (de Bruijn–Newman); Rodgers–Tao `Λ≥0` (FE-forced) ⟹ **RH ⟺ Λ=0 = the
  no-margin.** §4 Thm 6 (PROVED HERE): moment positivity ⇏ frequency positivity (witness `a_n=1+4^n`)
  — *the precise reason RH isn't a free byproduct of FE-positivity.* (→ [[bucket-the-no-margin]])

### Face 3 — CMV/OPUC unitarity, `|γ_k|<1` (#78 §12 — THE most direct)
- Via Arakelov `w=1−1/ρ` (`ArakelovW`: `|w|=1 ⟺ Re=½`), **RH ⟺ the secular CMV/OPUC operator is
  UNITARY ⟺ Verblunsky coefficients `|γ_k|<1 ∀k`.** Validated N=40 across **four L-functions** (ζ,
  Dirichlet β, Ramanujan Δ, elliptic 11a): all `|γ_k|=0.993–0.999` (no-margin AT the circle); off-line
  ⟹ `|γ_k|>1` detected robustly. *This IS "unitary holonomy."*

### Face 4 — the capstone `ι=κ` (#78 §14 — purest form)
- RH ⟺ **`ι=κ`** (the FE-inversion `w↦1/w` equals conjugation `w↦w̄` on the spectrum) ⟺ the secular
  operator's FE-involution coincides with its adjoint (FE-self-duality) ⟺ unitary/self-adjoint.
  **Pointwise case ledger-proven:** `sigmaConj_fixed_iff_critical`. *Unifies all faces:* orbit-size-2 =
  `|w_ρ|` on circle = CMV unitary = Jacobi self-adjoint = Hankel/Toeplitz PSD/PF = `Λ≤0`.

### Face 5 — Jacobi / Berry–Keating self-adjointness (#78 §9, §27)
- §9 Conjecture D: RH ⟺ the secular Jacobi operator `J` (source-pure, eigenvalues `−1/γ²`) is
  self-adjoint ⟺ `b_k>0 ∀k`; `J=−Δ+V` = lattice prime Schrödinger. §27 Berry–Keating/Connes: FE-invariant
  `u=s(1−s)=¼+γ²`; RH ⟺ `u_n` real ≥¼ ⟺ a secular operator in `u` positive self-adjoint (`Δ≥¼`).
  Ledger pointwise: `BerryKeating` (`berryKeatingU_sigma`, `..._re_ge_quarter_on_critical`,
  `..._nonreal_of_offCritical`).

### Face 6 — Hodge–Riemann positivity of the Weil representation (#78 §19–22 — the deepest)
- RH ⟺ **`Q_W ⪰ 0` ⟺ the Hodge–Riemann bilinear relations for the metaplectic/Weil representation of
  `SL₂(ℝ)`** (the theta-modularity group producing ξ's FE). Generators concrete: **the dBN heat flow
  `e^{tu²}` = the unipotent ample/Lefschetz class `X=u²`; the FE involution `σ` = the elliptic
  `S`-element (Fourier).** The Lefschetz iso `X^k` is FREE (the Weil rep itself); **RH = the
  Hodge–Riemann SIGNATURE.** Matches function-field hard Lefschetz generator-for-generator. Ledger:
  oscillator commutators `[H,X]=2X,[H,Y]=−2Y,[X,Y]=−4H` (`OscillatorAlgebra`). (→ [[bucket-time-and-non-holonomic-time]]: heat flow = the clock, FE = the Fourier element)

### Face 7 — the prime-lattice Schrödinger operator (#88 §8 — MOST ACTIONABLE) + Hilbert–Pólya (#90)
- §8 **Weil positivity = an explicit Schrödinger operator (PROVED HERE + certified):**
  `Q_W = H_W := −Δ_prime + V_arch` on `ℓ²` of the smooth numbers, with kinetic `−Δ_prime=Σ_p J_p`
  (commuting per-prime long-range Jacobi operators, **separable**, closed-form symbol, **indefinite**)
  and potential `V_arch` = the archimedean Toeplitz kernel (a **logarithmic confining potential**,
  certified to 1e-15). **`RH ⟺ H_W ≥ 0` ⟺ the log archimedean potential is dominated by the separable
  indefinite prime kinetic.** = the team's `Z_n ≻ A_n` in operator form. *The multiplicative side is
  fully diagonalized; only the domination is open.*
- #90 §7 **the Hilbert–Pólya operator = gen(G_L)** = `D` (Berry–Keating "xp", archimedean) + `{σ_p}`
  (prime dilations); RH ⟺ gen(`G_L`) self-adjoint, real spectrum `{γ}`. Naive HP fails because `D` is
  **type III** (continuous spectrum); the zeros = the **ABSORPTION spectrum (Connes)**, cut out by the
  prime/adele-class quotient (§7 = Connes' `L²_0`). **SEED-X (§8): `RH ⟺ [D, P_{prime-coinv}] = 0`** —
  "the two wings commute on the quotient." The MEAN is rigorous: `D=−i(x∂_x+½)` essentially
  self-adjoint, Berry–Keating Weyl law = the smooth Riemann–von Mangoldt count; the **fluctuations =
  the prime perturbation = the wall.** (→ [[bucket-time-and-non-holonomic-time]], [[bucket-the-seam-archimedean-obstruction]])

---

## Adjacent realizations (same gatekeeper, other languages)
- **Avila cocycle / dynamical localization (#68 SEED-D, #87 §5):** "unitary holonomy" = "`L=0`
  reducible cocycle"; RH = self-dual Avila-criticality everywhere; FE = Aubry duality `λ↔1/λ`;
  no-margin = no almost-reducibility strip (no spectral gap). Numeric: critical AMO `λ=1` has `L=0`.
- **Unitary holonomy of the completed flat connection (#91 §4):** adjoin the ∞-lane (Γ-weight =
  connection term) to the flat prime connection; **the FE IS the flatness of the completed
  connection;** RH = its boundary holonomy (on `Re=½`, `|w|=1`) is **UNITARY**. Candidate G5 verbatim,
  with flatness FORCED by the FE; candidate G3 made concrete. (→ [[G3-holonomy-dichotomy]])
- **Hodge-index (1,∞) signature (#89 §7):** explicit formula = an Arakelov intersection pairing
  `⟨Z, prime divisors⟩`; **RH ⟺ Hodge-index signature (1,∞)** = Weil/Bogomolov positivity = the team's
  `n₊=1` / `scForm_sigNeg` / CKS `±b²` core. RH = Bogomolov height-minimality of the spectrum (§1–4,
  `WCoordinate`).
- **Boundary unitarity / ghost-free CFT (#92 §3, #97 §2):** RH ⟺ `κ₋=0` ⟺ the prime bulk's holographic
  boundary dual is a **unitary CFT** (off-line zero = negative-norm ghost). (the ridgeline →
  [[bucket-A1-A2-unification-the-carrier]])
- **Exceptional point / PT-unbroken phase (#96 §1):** the no-margin is an **EXCEPTIONAL POINT**
  (eigenvalues AND eigenvectors coalesce). RH = the ζ-operator PT-UNBROKEN (real spectrum), pinned at
  the exceptional threshold. Certified toy `H(a,b)=[[ia,b],[b,−ia]]`. (→ [[bucket-the-no-margin]])
- **LP-limit (#98 Attack 5, PROVED):** each `σ_p` is a Pólya–Schur multiplier (`e^{x/p}∈LP`); every
  finite truncation `∏_{p≤P}σ_p` is LP-preserving; **RH ⟺ `∏_p σ_p` stays LP ⟺ ξ∈LP.** RH = a
  closedness/identification problem, not a positivity one (positivity is automatic along the family).
  Ledger floor: `MultiplierScaling` (`sigmaScale_splits`). (→ [[bucket-realization-and-fake-family]])

---

## The honest insufficiency note (don't let G5 alone "see RH")
- **#75 §2 (E)/(A)/(P) cuts:** the fakes (Davenport–Heilbronn) can satisfy **Hankel-positivity without
  being genuine** ⟹ **positivity (P) does NOT imply arithmeticity (A).** So candidate G5 (positivity/
  unitarity) **must be conjoined with the Euler-product cut (A)** to exclude fakes — G5 alone is
  insufficient. (→ [[bucket-realization-and-fake-family]]) This is the no-margin/integrality lesson:
  genuineness is the Euler cut, not the positivity cut.

---

## Status ledger for this bucket

| Face | Tier / grade | Ledger foothold |
|---|---|---|
| σ-fixed locus = critical line (Lemma 1) | verified computation | `sigmaConj_fixed_iff_critical`, `BoundaryModulus`, `ArakelovW` |
| `κ₋ = #off-line pairs` (finite carrier) | **ledger-proven** | `multiPair_carrier_exact_neg_inertia` |
| CMV unitary / `|γ_k|<1` | conjecture + numeric (4 L-fns) | `ArakelovW` |
| `ι=κ` capstone | pointwise **ledger-proven** | `sigmaConj_fixed_iff_critical` |
| Berry–Keating `u≥¼` | pointwise **ledger-proven** | `BerryKeating` |
| Hodge–Riemann `Q_W⪰0` (Weil rep) | conjecture; algebra ledgered | `OscillatorAlgebra` |
| `H_W=−Δ_prime+V_arch ≥ 0` | **PROVED HERE** + certified; domination open | — |
| HP = gen(`G_L`), `[D,P]=0` | conjecture; MEAN rigorous | — |
| infinite passage (all faces) | **OPEN core** (Nevanlinna/Krein–Langer mathlib gap) | `MeasureCarrier`, `CayleySchur` |

## Open core / the work package
**The infinite passage**, in one sentence: build the common difference-Galois group `G_L`, show its
**boundary representation is unitary**. Concrete: state G5 as `RH ⟺ m_ξ Herglotz on ℂ⁺`; pursue the
**one archimedean rigidity bound** (multiplicity estimate on `G_L`) that forces `κ₋(m_ξ)=0` — the same
bound that forces DSS (the carrier's jet). The multiplicative side is fully diagonalized; the sole
obstruction is the archimedean Γ-term ([[bucket-the-seam-archimedean-obstruction]]). **Conjoin with the
Euler cut (A)** so it rejects fakes.

## Cross-references
- [[bucket-A1-A2-unification-the-carrier]] — G5 = "unitary" (A1); same germ's jet = "faithful" (A2).
- [[bucket-the-no-margin]] — the no-margin (κ₋→0, `|γ_k|→1`, exceptional point) is G5's signature.
- [[bucket-the-seam-archimedean-obstruction]] — the sole open obstruction is the archimedean term.
- [[bucket-realization-and-fake-family]] — G5 alone passes fakes; must be conjoined with the Euler cut.
- [[bucket-time-and-non-holonomic-time]] — HP = the clock's generator; "RH = the clock preserves a norm."
- [[bucket-function-field-proving-ground]] — over `F_q`, G5 = "Frobenius is unitary" (Deligne).
- [[bucket-ledger-footholds]] — G5's positivity face has a real, growing Lean toolchain.
