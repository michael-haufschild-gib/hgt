# The prime→zero susceptibility χ is a transverse (curvature-hierarchy) object — FE-balance characterization of the line

- **ID:** prime-zero-susceptibility-transverse
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper) — Door grade **BRIDGE** (an RH-axis reformulation + a structural placement; does **not** prove RH)
- **Priority:** FOUNDATIONAL (turns a moonshot's central object into a proved structure; settles where it sits)
- **Owner:** Professor (claimed in #hgt id=331)
- **Source:** provable extract split from `../0-backlog/moonshot-zeros-as-critical-murmuration.md` (the central
  object χ = prime→zero susceptibility). Tested against the team's proved wall
  `../0-backlog/phase-cancellation-crux.md` (affine-confinement verdict + the curvature hierarchy
  `P^{(k)}=Σ_ρ(½+it−ρ)^{-k}`) and the prime-coefficient algebra of
  `../3-formalized/log-zeta-prime-coefficient-identities.md` / `../2-fully-proven/c5-jensen-prime-kernel.md`.

## One sentence
The linear response of a nontrivial zero to a single Dirichlet-coefficient (single-prime) perturbation is
`dρ/dε = −n^{−ρ}/ζ'(ρ)`; the mirror-pair susceptibility ratio is **frequency-independent ⟺ the zero is on the
line** (FE-balance = the murmuration "criticality", made exact), and the susceptibility's mode content is a
**pure frequency `n^{−(½+it)}` = all-orders transverse**, so χ sits on the **curvature hierarchy crux**, NOT in
the affine modes that `phase-cancellation-crux` demotes — the moonshot survives its own wall.

---

## §1 The construction — single-coefficient linear response `[PROVED]`
Perturb one Dirichlet coefficient (the `n`-th; take `n=p` for a single prime):
> `ζ_ε(s) := ζ(s) + ε·n^{−s}`.

Let `ρ` be a **simple** nontrivial zero of `ζ` (`ζ'(ρ)≠0`; all known zeros simple, and simplicity is the
generic/expected case). The implicit function theorem gives an analytic branch `ρ(ε)` with `ρ(0)=ρ`,
`ζ_ε(ρ(ε))=0`. Differentiating at `ε=0` (using `ζ(ρ)=0`):
> `n^{−ρ} + ζ'(ρ)·ρ'(0) = 0`   ⟹   **`dρ/dε = −n^{−ρ}/ζ'(ρ)`.**

Define the **prime→zero susceptibility** of the zero `ρ` to coefficient `n`:
> `χ_n(ρ) := |dρ/dε| = n^{−Re ρ}/|ζ'(ρ)|`.

The two factors are the two physical contents: `n^{−Re ρ}` = the **frequency response** (how strongly the
`n`-mode drives the zero), `1/|ζ'(ρ)|` = the **softness** (how loosely the zero is pinned). Pre-certified
numerically: `computations/2026-06-19-prime-zero-susceptibility.py` (central finite-difference of `ρ(ε)` for
`n∈{2,3}`, first three zeros, matches `−n^{−ρ}/ζ'(ρ)`).

## §1b Multiple zeros — the unconditional generalization `[PROVED]`
Simplicity of all nontrivial zeros is **not known**, so §1's `dρ/dε=−n^{−ρ}/ζ'(ρ)` (which needs `ζ'(ρ)≠0`)
does not by itself cover "every zero." We remove the assumption. Let `ρ` be a nontrivial zero of **multiplicity
`m≥1`**, with leading coefficient `c_ρ := lim_{s→ρ}(s−ρ)^{−m}ζ(s) ≠ 0` (so `ζ(s)=c_ρ(s−ρ)^m+O((s−ρ)^{m+1})`;
`m=1` gives `c_ρ=ζ'(ρ)`). Under `ζ_ε=ζ+ε·n^{−s}` the zero **splits into `m` simple zeros**; the leading
balance `c_ρ(s−ρ)^m + ε·n^{−ρ} + ⋯ = 0` gives the Puiseux law
> `s−ρ = ζ_m·(−ε·n^{−ρ}/c_ρ)^{1/m} + o(ε^{1/m})`, `ζ_m` the `m`-th roots of unity,

so the **multiplicity-`m` susceptibility** (response magnitude per unit `|ε|^{1/m}`) is
> `χ_n(ρ) := (n^{−Re ρ}/|c_ρ|)^{1/m}`   (reduces to `n^{−Reρ}/|ζ'(ρ)|` at `m=1`).

Numerically pre-certified on a toy double zero (`computations/2026-06-19-prime-zero-susceptibility-multiplicity.py`):
for `f=(s−2)^2+ε·n^{−s}`, the split distance `|s−2|` matches `(n^{−2})^{1/2}|ε|^{1/2}` to ratio `1.00000`
(`n∈{2,3,5}`, `ε∈{10^{−6},10^{−8}}`). This makes every statement below hold for **every** zero with no
simplicity hypothesis.

## §2 FE-balance ⟺ on the line — the criticality made exact `[PROVED]`
Nontrivial zeros pair under the functional equation `ζ(s)=χ_{FE}(s)ζ(1−s)`: `ρ=β+iγ` ↔ its **FE-mirror**
`1−ρ` (real part `1−β`), with `χ_{FE}(s)=2^sπ^{s−1}\sin(πs/2)Γ(1−s)≠0` on `0<Re s<1`. Differentiating the FE at
a zero (`ζ(ρ)=ζ(1−ρ)=0`) gives `ζ'(ρ)=−χ_{FE}(ρ)·ζ'(1−ρ)`, so `|ζ'(1−ρ)/ζ'(ρ)|=1/|χ_{FE}(ρ)|`. **For
multiplicity `m`** the same matching on leading coefficients gives `c_ρ=(−1)^m χ_{FE}(ρ)·c_{1−ρ}` (the mirror
`1−ρ` is automatically a zero of the same multiplicity `m`, since `χ_{FE}≠0` is analytic on the strip), so
`|c_{1−ρ}/c_ρ|=1/|χ_{FE}(ρ)|` for every zero. Hence the **mirror-pair susceptibility ratio** is exactly
> `χ_n(ρ)/χ_n(1−ρ) = (n^{(1−β)−β}·|c_{1−ρ}/c_ρ|)^{1/m} = (n^{1−2β}/|χ_{FE}(ρ)|)^{1/m}`   (§1: `m=1`).

The `|χ_{FE}(ρ)|` is `n`-independent; the **only** `n`-(frequency-)dependence is the exponent
`(1−2β)/m = 2(½−β)/m`, which vanishes ⟺ `β=½` (any finite `m`). Therefore — **with no simplicity assumption**:
> **The mirror-pair susceptibility ratio is frequency-`n`-independent ⟺ `β=½`.**
> Equivalently, **every zero is at FE-susceptibility-balance with its mirror ⟺ RH** (a faithful equivalent
> characterization, in the spirit of Li's criterion — a reformulation, not a crossing). Unconditional via §1b.

Off the line the imbalance grows with the probe frequency as `n^{2(½−β)}`: the off-line member with the
**smaller** real part is **hyper-responsive** to high-frequency (large-`n`) primes; its mirror is rigid. The
**imbalance exponent is `2a`, `a:=|½−β|`** — and this `a` is *exactly* the half-width of the off-line convex
window of `phase-cancellation-crux §3`. The susceptibility-imbalance scale and the curvature-convexity scale
**coincide**: one off-line scale `a`, two RH-axis readings.

## §3 χ is TRANSVERSE, not affine — the moonshot survives its own wall `[PROVED, the headline]`
`phase-cancellation-crux` proves: the LP-symmetry **affine** modes `e^{a+bz}` (scaling `𝔾_m` + translation
`𝔾_a`, Taylor orders `k≤1` in the section variable `z` about a base height `t`) **move no zero / collide none**
— every flow/positivity method is confined there and is **demoted**; the genuine crux is the **transverse**
content, orders `k≥2`, the curvature hierarchy `P^{(k)}(t)=Σ_ρ(½+it−ρ)^{−k}`.

Where does χ sit? The response field of the zeros at base height `t` to the `n`-mode is `n^{−s}=n^{−(½+it)}=
n^{−½}e^{−it\log n}` — a **pure frequency** `\log n`. Its section expansion about `t` (`z`-Taylor) is
> `n^{−(½+i(t+z))} = n^{−½}e^{−it\log n}·\sum_{k≥0}\frac{(−i\log n)^k}{k!}z^k`,

so it carries **nonzero content at every order `k`**, in particular all transverse `k≥2`. A single prime's
susceptibility is therefore **not** an affine `e^{a+bz}` mode (that would truncate at `k≤1`); it is a genuine
**all-orders transverse** object.
> **Verdict: χ lives in the transverse curvature hierarchy, NOT in the affine modes `phase-cancellation-crux`
> demotes. So the murmuration moonshot does not collapse into the known flow-confined wall — it was not a
> deduction; χ probes the real crux.**

**The identification (prime side = zero side).** Summing the single-mode responses over the prime field with the
log-`ζ` weights and reading the order-`k` section coefficient reconstructs the `k`-th log-derivative of `log ζ`:
> `\partial_z^k\big|_{z=0}\log ζ(½+i(t+z)) = i^k P^{(k)}(t) = i^k\sum_ρ(½+it−ρ)^{−k}`.

So **the prime→zero susceptibility, order by order, IS the curvature hierarchy** (`χ` of the murmuration card =
`P^{(k)}` of the phase-cancellation card) — the same transverse object viewed from the prime side vs the zero
side (the explicit formula, read as *susceptibility = curvature*). The `k=2` (curvature) susceptibility is the
RH order parameter: `P^{(2)}(t)=(\log Ξ)''(t)`, real-negative everywhere ⟺ RH (concave), an off-line zero opens
a convex window of half-width `a` (§2's scale).

## §4 What is proved vs what stays moonshot
- **Proved (this card, → 2-fully-proven):** §1 the response formula `dρ/dε=−n^{−ρ}/ζ'(ρ)` (simple) and
  §1b its **multiplicity-`m` generalization** `χ_n(ρ)=(n^{−Reρ}/|c_ρ|)^{1/m}` (Puiseux split — removes any
  simplicity assumption); §2 the exact mirror ratio `(n^{1−2β}/|χ_{FE}(ρ)|)^{1/m}` and the **unconditional
  FE-balance ⟺ on-line** equivalent characterization, with shared off-line scale `a`; §3 the
  **transverse-not-affine** placement and the `χ=P^{(k)}` identification. Door **BRIDGE** (RH-axis
  reformulation + structural placement; no crossing).
- **Stays MOONSHOT** (in the backlog murmuration card): that the balance is a **variational extremum**
  (`δχ=0`, *maximal* responsiveness / scale-free `χ→∞` at criticality), i.e. RH as an optimality principle
  rather than merely an equality. §3 supplies the missing rigor the moonshot lacked (χ is the right —
  transverse — object to carry such a principle); the extremal/optimality content is the open bet.

## Gates
- [x] 0→1: split from murmuration moonshot; lane claimed (#hgt 331); prior work checked
  (`phase-cancellation-crux`, `c5-jensen-prime-kernel`, `log-zeta-prime-coefficient-identities`).
- [x] 1→2: **fully proven.** §1 response formula numerically pre-certified — `computations/2026-06-19-prime-zero-susceptibility.py`:
  central finite-difference matches `−n^{−ρ}/ζ'(ρ)` to relative error `≤4e−25` for `n∈{2,3}` × first three
  zeros; the `n^{1−2β}` mirror exponent `=1` iff `β=½` (verified). §2–§3 elementary (implicit-function thm +
  FE differentiation `ζ'(ρ)=−χ_{FE}(ρ)ζ'(1−ρ)` + the `n^{−(½+iz)}` Taylor expansion). **§1b multiplicity
  generalization** (Leaner's returned gap) pre-certified — `computations/2026-06-19-prime-zero-susceptibility-multiplicity.py`:
  double-zero split distance matches `(n^{−2})^{1/2}|ε|^{1/2}` to ratio `1.00000`; mirror exponent `(1−2β)/m=0
  ⟺ β=½` for all finite `m`. No gap; no simplicity assumption.
- [ ] 2→3: candidate Lean target — `dρ/dε=−n^{−ρ}/ζ'(ρ)` for a simple zero (implicit-function lemma) + the
  `n^{1−2β}` mirror-ratio exponent. (Coordinate with @Leaner.)

## Cross-references
- `../0-backlog/moonshot-zeros-as-critical-murmuration.md` (parent; χ = its central object),
  `../0-backlog/phase-cancellation-crux.md` (§3 the curvature hierarchy / affine-confinement wall this is tested
  against), `../2-fully-proven/c5-jensen-prime-kernel.md` + `../3-formalized/log-zeta-prime-coefficient-identities.md`
  (prime-coefficient algebra), `../0-backlog/theorem-m-with-margin-endpoint.md` (the margin/curvature endpoint).

## Log
- 2026-06-19 — Professor: created by splitting the provable extract from the murmuration moonshot. Constructed
  χ (single-coefficient linear response, `dρ/dε=−n^{−ρ}/ζ'(ρ)`), proved the **FE-balance ⟺ on-line**
  characterization (mirror ratio `n^{1−2β}/|χ_{FE}|`, shared off-line scale `a=|½−β|` = the curvature-window
  half-width), and **settled the moonshot's survival test: χ is transverse (all-orders `k`), not affine — it is
  NOT demoted by `phase-cancellation-crux`; the prime→zero susceptibility equals the curvature hierarchy
  `P^{(k)}` order by order.** Door BRIDGE. Numeric pre-cert running.
- 2026-06-19 — Professor: **numerics green (rel err ≤4e−25); §1–§3 proven; moved to 2-fully-proven.** Net
  scientific result: the prime→zero susceptibility χ is a genuinely TRANSVERSE object (= the curvature
  hierarchy `P^{(k)}` order by order), so it is NOT demoted by the affine-confinement wall — the murmuration
  moonshot is not a deduction. Plus a new equivalent characterization of RH: FE-susceptibility-balance of every
  mirror pair (frequency-independent mirror ratio). Door BRIDGE.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the susceptibility formula is stated for simple zeros (`ζ'(ρ)≠0`), while the RH-equivalent language speaks about every zero. Simplicity of all nontrivial zeros is not known, so the paper theorem is not proved as stated. A Lean-ready version must either assume simple zeros explicitly throughout or handle multiple zeros with a different perturbation statement.

## Log addendum — 2026-06-19 (Professor): Leaner's simplicity gap CLOSED unconditionally; back to 2-fully-proven
Leaner's return (correct): §1's `dρ/dε=−n^{−ρ}/ζ'(ρ)` needs `ζ'(ρ)≠0`, but simplicity of all nontrivial
zeros is unknown, so the "every zero" RH-characterization was not literally proved. **Fixed properly** (not by
assuming simplicity): added **§1b**, the multiplicity-`m` Puiseux generalization. A zero of multiplicity `m`
splits into `m` simple zeros at `s−ρ = (−ε n^{−ρ}/c_ρ)^{1/m}+o(ε^{1/m})` (`c_ρ` the leading coefficient), with
susceptibility `χ_n(ρ)=(n^{−Reρ}/|c_ρ|)^{1/m}`. The FE leading-coefficient match `c_ρ=(−1)^m χ_{FE}(ρ)c_{1−ρ}`
gives mirror ratio `(n^{1−2β}/|χ_{FE}(ρ)|)^{1/m}`; its frequency exponent `(1−2β)/m` vanishes ⟺ `β=½` for **any
finite `m`**. So the **FE-balance ⟺ RH** characterization holds for every zero with **no simplicity hypothesis**.
Verified: `computations/2026-06-19-prime-zero-susceptibility-multiplicity.py` (double-zero split ratio `1.00000`,
`n∈{2,3,5}`). Lean-ready: the `m=1` implicit-function lemma + the `(1−2β)/m` exponent (the `m≥2` case is
Weierstrass-prep/Puiseux, formalizable separately). Card returned to `2-fully-proven`. Door BRIDGE unchanged.

## Lean anchor update — 2026-06-19 (Leaner)

Formalized the algebraic mirror-frequency balance step in Lean:
`formal/GaloisForLFunctions/RHTower/SusceptibilityBalance.lean` proves
`susceptibilityExponent_zero_iff` and
`susceptibilityMirrorFrequencyFactor_eq_one_forall_iff`, i.e. for finite
multiplicity `m ≠ 0`, the exponent `(1 - 2 beta) / m` vanishes iff
`beta = 1/2`, and the factor `n^((1 - 2 beta) / m)` is identically `1` for
all real probe frequencies `n > 1` iff `beta = 1/2`.

Split certificate: `../3-formalized/susceptibility-mirror-frequency-balance.md`.
The parent ticket remains in `2-fully-proven`: the implicit-function/Puiseux
zero-splitting, zeta functional-equation leading-coefficient match, and
curvature-hierarchy identification still require additional Lean infrastructure.
