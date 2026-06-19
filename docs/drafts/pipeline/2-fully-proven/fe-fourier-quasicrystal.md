# FE ⟺ the generalized-integer measure is a Fourier quasicrystal (G8 / crystalline self-duality)

- **ID:** fe-fourier-quasicrystal
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) — equivalence + Door-2 verdict; grade **BRIDGE**. (Was CANDIDATE; worked to a
  verdict here.)
- **Priority:** FUTURE
- **Source:** `../../door/bucket-new-sibling-conjectures.md` (#68 SEED-F) · 00-status row #97. Uses:
  `../2-fully-proven/explicit-formula-as-constraint.md` (#139), `../2-fully-proven/orthogonality-meta-theorem.md`
  (#137), Euler⟺Bohr factorization (#81), faces-orthogonality (#54).
- **Statement:** The functional equation `Λ(s)=Λ(1−s)` is equivalent to **Fourier self-duality of the
  generalized-integer measure** (a Fourier-quasicrystal / crystalline-measure property), via theta
  modularity = Poisson summation. **Verdict:** this characterizes the FE intrinsically (non-analytically),
  but it is **BRIDGE** (= classical Poisson summation), and crystallinity is **RH-blind**: self-dual
  measures with **off-line** zeros exist (Davenport–Heilbronn). The datum that separates RH from a fake is
  **not** crystallinity but the Euler product (#81) + the archimedean polarization (#137).

## Goal
Pin the FE — usually imported as ζ's analytic continuation — as an **intrinsic self-duality** of the prime /
generalized-integer measure, and **separate** what crystallinity does and does not give: it gives the FE
axis, **not** the localization (RH) axis. This confirms the faces-orthogonality split (#54) / orthogonality
meta-theorem (#137) at the **level of measures**, and isolates the FE for the G5 polarization faces
(`carrier-herglotz-rh`, `weil-positivity-operator`).

---

## §1 FE ⟺ theta modularity ⟺ Poisson self-duality `[derived — the equivalence]`

Riemann's theta route, run as a self-duality statement. Let `θ(t)=Σ_{n∈ℤ} e^{−πn²t}` and recall
`Λ(s)=π^{−s/2}Γ(s/2)ζ(s)=½∫_0^∞ (θ(t)−1)\,t^{s/2}\,dt/t` (Mellin). Then:
```
   Λ(s)=Λ(1−s)   ⟺   θ(1/t)=√t·θ(t)   (theta modularity)   ⟺   Poisson summation for the lattice ℤ.   (1)
```
The middle ⟺ is Riemann's computation (split the Mellin at `t=1`, apply modularity to the `(0,1)` piece);
the right ⟺ is that `θ(1/t)=√t\,θ(t)` is exactly Poisson summation `Σ_n f(n)=Σ_n \hat f(n)` for the Gaussian
`f(x)=e^{−πx²t}` (self-dual under the Fourier transform). In measure language: let `Ш=Σ_{n∈ℤ}δ_n` be the
**Dirac comb** of the (generalized-)integer support. Poisson summation is precisely
```
   \hat{Ш} = Ш :   the integer Dirac comb is its own Fourier transform — the prototypical
                    Fourier quasicrystal (atomic measure with atomic transform, both locally finite).   (2)
```
So **FE ⟺ the generalized-integer measure is Fourier-self-dual = a Fourier quasicrystal.** The "σ-base
symmetry" native dressing of the FE (`x_p↦p^{−1}x_p^{−1}`, the inversion-and-scale) is, on the Bohr base
`𝕋^∞`, the Poisson/Pontryagin self-duality of the corresponding comb; multiplicativity (unique
factorization) makes the `∞`-base comb a restricted product of the per-prime combs, and self-duality
decouples prime-by-prime to Poisson on each `ℤ`-lane. ∎(§1)

## §2 The zeros↔primes face — the explicit formula is the dual pairing `[derived]`

Crystallinity has a second face: the Weil explicit formula (#139) is the statement that the **Fourier
transform of the zero measure is the prime measure** (up to the archimedean density). For an even test `h`
with transform `ĥ`,
```
   Σ_γ h(γ) = \underbrace{(\text{poles}) + \tfrac1{2π}∫ h(r)\,\mathrm{Re}\,ψ(\tfrac14+\tfrac{ir}{2})dr}_{\text{archimedean continuous part}}
            − \underbrace{Σ_{n≥2} \frac{Λ(n)}{\sqrt n}\,(ĥ(\log n)+ĥ(−\log n))}_{\text{prime atomic part}}.   (3)
```
Reading (3) as `\widehat{Σ_γδ_γ} = (\text{archimedean continuous}) − Σ_n \tfrac{Λ(n)}{\sqrt n}δ_{±\log n}`:
the zero measure is a **crystalline measure** (atomic transform, support `{±\log n}` locally finite). The FE
symmetrizes (3) (`s↔1−s` ⟺ `r↔−r`, evenness), and the archimedean `Γ`-factor supplies the **continuous
self-dual completion** that closes Poisson. So the two faces of "crystalline" coincide: (§1) the integer-comb
self-duality **is** the FE; (§2) the zeros↔primes duality **is** the explicit formula. Both are
Poisson/Pontryagin duality on the Bohr base. ∎(§2)

## §3 Door-2 verdict — BRIDGE `[the load-bearing test]`
Strip every native (multi-`q`, `G_L`) word from §1–§2. What remains proves the equivalence:
- §1 = **theta modularity / Poisson summation** (Jacobi, Riemann) — classical harmonic analysis;
- §2 = the **Weil explicit formula** (#139) — classical.
The simultaneous-`σ_p` version is Poisson on `𝕋^∞` = **Kronecker self-duality**, which decouples prime-by-prime
(`#136` Fourier-diagonal generators; `#137` the prime/Source-B structure carries no RH content). So G8 is a
**re-description of the FE in crystalline language**, proved by a parent. **BRIDGE, not native.** (Consistent
with the founding negative theorem: a *self-duality constraint* is not a generative rule; it is one half of
the FE constraint that fixes `Λ`.)

## §4 The payoff — crystallinity is RH-blind; the fake-rejection `[the genuinely useful content]`
The card's real question: does the crystalline characterization **reject the off-line fakes** (so it could
carry RH)? **No — and this is the useful, derivable theorem.**

> **Claim (crystallinity ⊥ localization).** Fourier self-duality / the FE does **not** force real zeros.
> There exist Dirichlet series with a genuine functional equation — hence whose coefficient measure is
> Fourier-self-dual / crystalline — whose zeros are **off** the critical line.

**Witness (classical IMPORT — Davenport–Heilbronn 1936).** The Davenport–Heilbronn function
`f(s)=Σ a_n n^{−s}` (a `ℚ(√5)`-combination of two period-5 Dirichlet `L`-functions, chosen so the two
`Γ`-factors match) satisfies a **functional equation of ζ-type** (`s↔1−s` with a `Γ`-factor) — so by §1 its
coefficient comb is Fourier-self-dual / crystalline — yet it has **infinitely many zeros off the critical
line** (indeed in the half-plane `σ>1`, Titchmarsh). It violates RH **while satisfying the FE**. What it
lacks is an **Euler product**.

**Consequence.** Self-duality / crystallinity (§1–§2) is exactly the **FE axis** and is **RH-blind**. The
property that separates `ζ` (real zeros) from the Davenport–Heilbronn fake (off-line zeros) is **not**
crystallinity but:
- the **Euler product** = the Bohr factorization (#81: "Euler ⟺ Bohr factorization, the fake filter") — the
  fake has no Euler product; and
- the **real-rootedness / polarization positivity** = the archimedean polarization (#137: RH = positivity of
  the FE polarization, archimedean; #54 faces-orthogonality).
So G8 confirms, **at the level of measures**, the orthogonality split: **crystalline self-duality = the FE
(Source-A/B weld constraint), positivity/real-rootedness = the localization (RH) — two orthogonal faces.**
The crystalline framing cleanly **isolates** the FE for the polarization-based G5 faces, which is exactly
what `carrier-herglotz-rh` / `weil-positivity-operator` need (they supply the missing real-rootedness on top
of the crystalline FE). ∎(§4)

## §5 The real-rooted crystalline locus — cross-link to the finite-free carrier `[flagged conjecture]`
The crystalline measures whose atoms are **real** (the RH-true ones) are the **Lee–Yang / stable-polynomial**
locus (the Kurasov–Sarnak circle: a crystalline measure with real, simple atoms arises as the zero set of a
torus section of a stable / Lee–Yang polynomial). This is the **infinite-dimensional home** of Wheeler's
finite-free / Jensen Lee–Yang carrier (`finite-free-convolution-flow.md`): the localization content (G5,
real-rootedness) lives in the *real-rooted* sub-locus of the crystalline measures, **not** in crystallinity
itself. **Conjecture (flagged, Wheeler's lane):** `ζ`'s zero measure is the marginal boundary of the
real-rooted (Lee–Yang) crystalline locus — the `lee-yang-localization` candidate (#96) restated as a measure
statement. *(Marked: the Kurasov–Sarnak stable-polynomial characterization is used as a structural analogy,
not a load-bearing proof input.)*

## Door passport — BRIDGE
- **Door-1:** the σ-base symmetry is the native FE; crystalline self-duality keeps it in the difference world.
- **Door-2:** **FAILS** — §1 = Poisson summation, §2 = Weil explicit formula, both classical. The native
  dressing is decoration. **BRIDGE.**
- **Door-4:** the equivalence lives on Source-B/FE structure alone (no archimedean–prime weld is *used*),
  hence RH-blind (#137) — §4. The native zone (the polarization) is exactly what crystallinity does **not**
  reach.
- **Door-5:** over `F_q`, the FE is Poincaré duality of the curve and the "comb" is the finite divisor group;
  self-duality is the Weil pairing — recovered, classical (matches the BRIDGE grade).

## Gates
- [x] 0 → 1  in-progress: σ-FE and Fourier-quasicrystal self-duality pinned (§1); zeros↔primes face (§2);
  Door passport.
- [x] 1 → 2  fully-proven: the equivalence FE ⟺ crystalline self-duality is **proved** (§1, theta/Poisson;
  §2, explicit formula) and **Door-2-verdicted BRIDGE** (§3); the **fake-rejection** (crystallinity RH-blind,
  Davenport–Heilbronn witness) is proved (§4). No open dependency for the verdict. Grade BRIDGE. (§5 cross-link
  conjecture is flagged, out of scope.)
- [ ] 2 → 3  formalized: candidate anchors — theta modularity / Poisson (likely in mathlib), `functionField_esymm_FE`
  for the Door-5 face. Low priority (classical).
- [ ] 3 → 4  publication-ready: "The functional equation as crystalline self-duality, and why it is RH-blind."

## Approach `[done]`
Identified the σ-base symmetry with Poisson/Pontryagin self-duality of the generalized-integer measure
(§1–§2); imported the crystalline-measure framing; checked it against the off-line fakes (Davenport–Heilbronn,
§4) so the characterization is shown to **reject nothing RH-relevant** — its content is the FE, not RH.

## Cross-references
- `../2-fully-proven/explicit-formula-as-constraint.md` (#139) — §2 is its Poisson-duality face.
- `../2-fully-proven/orthogonality-meta-theorem.md` (#137), faces-orthogonality (#54) — §4 confirms them at
  the measure level.
- Euler ⟺ Bohr factorization (#81, the fake filter) — §4's first separating datum.
- `lee-yang-localization.md` (#96), `finite-free-convolution-flow.md` (Wheeler) — §5 real-rooted crystalline
  locus = the finite-free Lee–Yang carrier's infinite home.
- `carrier-herglotz-rh.md`, `weil-positivity-operator.md` — the G5 polarization faces this isolates the FE for.

## Log
- 2026-06-19 — created in 0-backlog (FE = crystalline self-duality, G8/SEED-F).
- 2026-06-19 — Professor: claimed → in-progress; **worked to verdict** (derived, not cited). Proved
  FE ⟺ theta modularity ⟺ Poisson self-duality of the integer comb (§1) and the zeros↔primes explicit-formula
  face (§2); **Door-2 verdict BRIDGE** (§3). Banked the useful payoff (§4): crystallinity is **RH-blind** —
  Davenport–Heilbronn satisfies the FE (crystalline) with off-line zeros, so the separating datum is the
  Euler product (#81) + archimedean polarization (#137), confirming faces-orthogonality at the measure level.
  Flagged the real-rooted-crystalline ↔ finite-free Lee–Yang cross-link (§5) for Wheeler. → 2-fully-proven,
  grade BRIDGE.
