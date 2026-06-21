# 09 — Pre-print Draft: The Strongest Provable Claims of the Current Research

**Working title.** *The Completed Zeta Object as a Constraint-Preserving Transport System: Proven
Structural Reductions, a Faithful Off-Line Index, and the Localization of the Riemann Obstruction to
a Single Archimedean Positivity.*

> **Status of this draft.** This is a *consolidation* pre-print: it states only what the current
> research has **provably established**, separates it cleanly from what remains conjectural, and
> **claims no proof of the Riemann Hypothesis**. Most proven results below are graded **BRIDGE** —
> they reorganize classical mathematics into the constraint-transport frame and are accompanied by
> machine-checked (Lean 4, axiom-clean) formalizations of their algebraic cores. The genuinely new
> content is *organizational and locating*: a complete decidable Source-A/B classifier, the
> linear-floor⊊algebraic-apex separation, the identification of the seam with the missing single
> Frobenius, a formalized faithful off-line index, and an affine-confinement diagnosis of why
> flow/positivity methods cannot cross the wall. Nothing here is asserted beyond the source corpus.

---

## Abstract

We develop the completed Riemann object `Λ = Γ∞·ζ` not as a scalar amplitude but as a
**constraint-preserving logarithmic transport connection** `ω = d log ξ`, equivalently the weld
`H(s) = ∂_s log Λ(s) = A(s) + P(s)` of an archimedean generator `A = ∂_s log Γ∞` and a prime term
`P = ζ'/ζ`. We prove: (1) `Λ` is fixed by the order-2 functional-equation constraint, not propagated
by a flow, which re-poses Hilbert–Pólya; (2) a complete, decidable invariant — σ-orbit-balance —
separates the two sources of hypertranscendence and localizes the unique archimedean (Source-A)
place to a single orbit; (3) the seam invariant **corank** is the number-theoretic shadow of the
*missing single Frobenius* (`= ∞` over ℚ, `= 1` over `F_q`), and its **linear floor** `corank = ∞`
(Baker, proven) is strictly weaker than the **algebraic apex** `trdeg = ∞` (Schanuel, open); (4)
RH-positivity is the positivity of the archimedean functional-equation polarization and is **not
definable on the prime structure**; (5) a faithful Krein–Langer index `κ₋ = #off-line zero-pairs`
(machine-formalized) satisfies `RH ⟺ κ₋ = 0`, with a single off-line zero forcing `κ₋ = 2`; (6) every
flow/positivity method is confined to the order-preserving affine `ax+b` orbit and cannot reach the
transverse seam where the obstruction lives. We document a reproducible empirical *weld phase
carrier* that distinguishes the true analytic continuation from finite-Euler and random-phase
controls in the critical strip, and we are explicit about the central open question — whether this
carrier is a native hypertranscendence invariant or detects only "analytic continuation ≠ finite
truncation." We conclude by locating the Riemann obstruction at a single archimedean positivity that
is **tool-independent** across ten distinct reformulations.

---

## 1. Framework: the constraint-transport object

`[FRAMEWORK]` The completed object satisfies the symmetric functional equation `Λ(s) = Λ(1−s)`. We
read its logarithmic derivative as a transport one-form
```
   H(s) = ∂_s log Λ(s) = A(s) + P(s),   A(s) = ∂_s log Γ∞(s),   P(s) = ζ'/ζ(s),
```
with the reflection law `H(s) = −H(1−s)` (as a one-form, `r*(H ds) = H ds`, `r(s)=1−s`). The two
summands are the field's two native generators: the archimedean differential generator `∂_s`
(dilation, `𝔾_m`) and the infinite prime difference base `{σ_p}` (translation-by-`log p`, `𝔾_a`),
on the affine group `𝔾_a ⋊ 𝔾_m` with **universal curvature** `[∂_s, M_p] = −log p`. The weld is the
seam; the seam is `Fix(ι) = {Re s = ½}`, `ι : s ↦ 1−s`.

This frame is the operational form of the founding principle (Hölder 1887): *the object is fixed by
a constraint, not propagated by a flow* — hypertranscendence is precisely the absence of a
generative (algebraic-differential) rule.

---

## 2. Proven results

Each result is stated with its register; "BRIDGE" denotes a locating/structural theorem that reduces
to a named classical parent when the multi-`q` vocabulary is stripped. Lean anchors are axiom-clean
(`[propext, Classical.choice, Quot.sound]`, `lake build` green, zero `sorry`).

**Theorem 1 (Constraint, not flow). `[PROVED — BRIDGE]`**
`Λ` is fixed by the involution `ι` (`ι² = id`, generating `ℤ/2`, *not* a one-parameter flow `ℝ`),
with `Fix(ι) = {Re s = ½}`. The flow that the prime structure (Source B) carries is the Kronecker
flow on `𝕋^∞`, whose spectrum is the prime frequencies `{log p}` (RH-blind by equidistribution),
**not** the zeros. Any operator with spectrum the zeros is a positivity, hence archimedean (Theorem
4); the zeros are an adelic spectrum (Connes 1999), realized only on an archimedean-inclusive space.
*Consequence:* Hilbert–Pólya is re-posed — the governing object is the constraint `ι` on the
archimedean-polarized space, and `RH ⟺ ι` acts unitarily.
*Lean:* `sigma_involutive`, `sigmaConj_fixed_iff_critical`, `primeLogFrequency_eq_zero_iff`.

**Theorem 2 (The two sources; a complete decidable classifier). `[PROVED — BRIDGE]`**
For a rank-1 difference module with multiplier `a`, `a` is constant-up-to-coboundary (CC, holonomic,
Source B) **iff** `div(a)` has σ-orbit-degree zero on every orbit. The Γ-multiplier `a(z) = z` has
`div(z) = [0] − [∞]`, `deg_ℤ(z) = +1 ≠ 0`: the archimedean place is the **unique** σ-orbit-unbalanced
(Source-A) place, with the imbalance localized to the single orbit `ℤ`; every prime lane is balanced.
The functional equation welds them: `C5 = {the one non-CC place} × {the CC places}`.
*Lean:* `orbitDegree_*`, `eq_sum_single_sub_base_of_orbitDegree_zero`, `ccGaugeMultiplier_eq_const`.

**Theorem 3 (The seam invariant; linear floor ⊊ algebraic apex). `[PROVED — BRIDGE]`**
The difference-Galois corank is one invariant with three faces (holonomicity, continuation
transcendence, weight torus): `corank = ∞` over ℚ (unique factorization), `corank = 1` over `F_q`
(one Frobenius). The gap `∞ − 1` is the archimedean seam = the *missing single Frobenius*. Moreover
`corank` is **inherently linear**:
```
   corank = ∞  ⟺  {log p} ℚ-LINEARLY independent          (Baker — PROVEN),
   trdeg  = ∞  ⟺  {log p} ℚ-ALGEBRAICALLY independent      (Schanuel — OPEN),
```
and since `trdeg ≤ corank` is only an upper bound, **`corank = ∞` does not force `trdeg = ∞`**: the
linear floor is strictly weaker than the algebraic apex, and the gap is exactly
Schanuel-for-prime-logs. The graded corank `corank^{(T)}` interpolates them; the first open rung is
`corank^{(2)}` (open even for `{log 2, log 3}`; the pairwise-homogeneous bottom is settled by
Gelfond–Schneider).
*Caveat (honest):* the naive reading "the obstruction is `corank = ∞`" is **false** — twin witnesses
with identical native invariants can have `trdeg = corank` or `trdeg < corank`; the obstruction is
value-arithmeticity, which the seam invariant is provably blind to. *Lean:* `linearIndependent_log_primes`,
`finitePrimeLogAnnihilator_eq_singleton`, `archimedean-corank-no-collapse`.

**Theorem 4 (Orthogonality of independence and positivity). `[PROVED — BRIDGE]`**
RH-positivity is the positivity of the functional-equation polarization (Weil), and that polarization
is archimedean: the prime category `𝓜` admits **no** polarization (a self-duality `M ≅ M^∨` would
force `g_p = g_p^{-1}`, i.e. `g_p = ±1`, false for Euler multipliers). Therefore **no statement
provable on the prime structure alone is RH-bearing**: independence (the prime engine) yields
equidistribution/variance, constitutively blind to correlation = positivity = RH. This predicts the
`F_q`/ℚ split exactly: `polarization ⟺ single Frobenius ⟺ corank 1 ⟺ F_q`. *Lean:*
`rankOne_noSelfDualMultiplier_of_sq_ne_one`.

**Theorem 5 (A faithful off-line index). `[PROVED — BRIDGE + Lean]`**
For the completed carrier `M = −Ξ'/Ξ` (`Ξ(t) = ξ(½+it)`), the negative inertia (Sylvester /
Krein–Langer index) is `κ₋ = #off-line conjugate zero-pairs` exactly; a single off-line zero,
FE-doubled, forces `κ₋ = 2`. Hence `RH ⟺ κ₋ = 0`. The index is **faithful** (a signed integer), not
a measured density — completion by the archimedean Γ-factor is what makes it a finite integer (the
raw `−ζ'/ζ` has `κ = ∞` from trivial zeros). Equivalently, in the Weil explicit-formula quadratic
form `Q_W` of signature `(1|∞)`, `RH ⟺ Q_W ⪰ 0`, with the obstruction confined to the single
archimedean direction `V_arch = Re ψ`. *Lean:* `multiPair_carrier_exact_neg_inertia`,
`fe_quadruple_kappa_two`, `bezout_eq_residue_gram`, `superzeta_coeff_eq_powerSum`,
`spectralTorelli_faithful`.

**Theorem 6 (Affine confinement of flow methods). `[PROVED — BRIDGE]`**
Decompose the root-displacement space by degree in node position. The large-value content lies in the
order-preserving affine subspace `⟨1, r⟩ = 𝔾_a ⋊ 𝔾_m` (scaling + translation), which scales every
gap by `a > 0` and therefore **cannot collide roots at any degree**. The RH-collision danger lies
entirely in the transverse seam `[𝔾_a, 𝔾_m]` — the higher log-derivatives
`P^{(k)}(t) = Σ_ρ (½+it−ρ)^{−k}` (`k ≥ 2`), the Laguerre–Turán / Hankel hierarchy. Its leader is
classical: `(log Ξ)''(t) = Σ_ρ (½+it−ρ)^{-2} < 0 ⟺ log|ξ(½+it)|` concave under RH; an off-line
quartet forces a local convex anti-smoothing window `2(a²−τ²)/(a²+τ²)²`, `|t−γ| < a`, `a = |½−β|`.
*Consequence:* every flow / positivity / de-Bruijn / energy / Laguerre method is affine-confined and
cannot reach the seam — *Hölder made mechanical*. (Numerically certified to ≤1e-18.)

---

## 3. Empirical result: the weld phase carrier

`[OBSERVED]` Define the phase-carrier defect `Δ(σ,t) = max(log|A|, log|P|) − log|A+P|`. In the
critical/left strip (strongest `σ ∈ [0.3, 0.5]`, fading through `σ ≈ 0.7`), the true analytic
continuation produces a persistent, structured, **positive** `Δ` that: (a) finite Euler truncations
do not reproduce even as `N → ∞` (amplitude grows, `Δ`-median stays `≈ 0`); (b) amplitude-matched
random-phase surrogates do not reproduce; (c) collapses to the finite/right-strip value at `σ > 1`.
The effect persists after regressing out all amplitude features (`σ=0.3` residual gap `+0.45` over
controls) and is corroborated by a faithful-index separator: across independent high-precision probes
(Weil–Gram conductor-5, high-`dps` reality firewall, level-repulsion, pollution-free Spec₂), genuine
ζ presents an all-real carrier (`κ₋ = 0`, recovering the actual `γ_n`) while a Davenport–Heilbronn
control presents off-line structure (`κ₋ ≥ 1`, e.g. negative Weil–Gram directions `−11.21, −2.22,
−0.45, −4.70` at off-line heights vs `+1.84..+2.96` for genuine `χ_odd`). Full numbers and controls:
`06-experimental-findings.md`.

`[OBSERVED — sharpest sub-structure]` Completing `ζ'/ζ → ξ'/ξ` exactly equalizes the two `σ=½±δ` lane
magnitudes at `σ=½` (imbalance `→0`) and reroutes the residual into pure relative phase — the
Γ-factor acting as an archimedean boundary-condition operator (the "Berry two-path completion
switch"). The off-line FE-quartet curvature above is the exact local-pole geometry of this seam.

---

## 4. The Riemann obstruction, located

Combining Theorems 4–6, the obstruction to RH is **one archimedean positivity**, expressible in
ten equivalent forms — `κ₋ = 0`; `Q_W ⪰ 0` (signature `(1|∞)`); positivity of the FE-polarization;
`m_ξ ∈ N₀`; the two-condition `H ⪰ 0 ∧ H' ⪰ 0`; the uniform-in-`d` Hankel hierarchy `det H_d ≥ 0
∀d,t`; `Ω ≽ Π`; G5 unitary holonomy; the semilocal `A_arch − Σ_p P_p ≥ 0`; the Hodge intersection
form of the (non-existent) `Spec ℤ ×_{F₁} Spec ℤ`. That these all reduce to the same positivity is a
**tool-independence** (a conservation law), not a coincidence — and it is *distinct* from the
realization apex (`ω = 0`, Schanuel-for-prime-logs), since **`ω = 0 ⇏ RH`** (already over `F_q`). The
two apexes are joined only at the archimedean seam; the project's "G1–G4 forces G5" aim is therefore
false as stated, and the correct picture is two apexes, one value-arithmetic, one positivity.

---

## 5. Honest scope and the central open question

This pre-print proves **no** new analytic fact about the location of the zeros. Its theorems are
**BRIDGE** — they relocate and formalize, they do not cross the wall. The empirical carrier is
`[OBSERVED]` and **has not been tested against the decisive surrogate ladder**: an FE-exact,
correct-zeros analytic fake (a Davenport–Heilbronn-type object that has ζ's symmetry and zeros but is
*not* hypertranscendental). The unresolved question on which the program turns is:

> Is the weld phase carrier a genuine *native hypertranscendence invariant* (a new transcendence
> detector), or does it detect only that *analytic continuation ≠ finite truncation* — true,
> structural, but already known?

Until the surrogate-ladder experiment runs, the carrier is labelled `[CONJECTURE]` "native HT
invariant," with moderate confidence for non-reducibility to finite truncation and low-to-moderate
confidence for native-vs-merely-analytic. The genuine open cores are stated in
`08-conjectures-required.md`: the uniform-in-`d` positivity (RH axis), Schanuel-for-prime-logs (value
axis), and the source-measure bridge that would connect the transport signatures to off-seam
exclusion.

---

## 6. Conclusion

The completed zeta object is most coherently described as a constraint-preserving, coupled-lane,
measure-covariant, Berry-interfering phase-space transport of `d log ξ`, fixed by the order-2 mirror
constraint with seam `Re = ½`. We have proven, and in large part machine-formalized, the structural
spine of this description: constraint-not-flow, the complete Source-A/B classifier, the
corank/missing-Frobenius seam with its linear-floor⊊algebraic-apex separation, the orthogonality of
independence and positivity, a faithful off-line index, and the affine-confinement of flow methods.
The Riemann obstruction is thereby located — as a single, tool-independent archimedean positivity,
distinct from and joined only at the seam to the value-arithmetic (Schanuel) apex. What remains is
the wall itself, in the precise forms catalogued here, together with the one experiment that would
tell us whether the transport carrier is native to hypertranscendence or a shadow of analyticity.

---

## Appendix A — Lean-formalized lemma index
See `07-theorems-and-lemmas-required.md` §2 (axiom-clean bricks).

## Appendix B — Source corpus
Light tower `publications/hgt/docs/experiments/draft.md`; synthesis `publications/hgt/logs/synthesis.md`;
`publications/hgt/docs/drafts/pipeline/{2-fully-proven,3-formalized,5-failed}`; `docs/rh-corp/`;
`docs/where_we_stand/`. Consolidated companions: `01`–`08` in this directory.

> **Reminder.** This is a consolidation artifact, not a claim of priority or of a solved problem. All
> forward statements are register-labelled; no RH proof is asserted.

---

## Appendix — Preprint positioning and the guardrail (incorporated from the GPT consolidation pass)

**Recommended posture** (so the draft never over-claims):
- State the **promoted BRIDGE theorems** (§2 Theorems 1–6) as the paper's actual *results*.
- State the **completed-transport interpretation** as a *synthesis* of those results, not a result.
- State the **light-tower carrier** as an *experimental and conjectural target*.
- State the **RH bridge** as an *open theorem package* (the 5 forms of `03-theorems-toward-rh.md`
  Appendix), not as evidence RH is proved.
- Use the **no-go acceptance standard** (`05-light-tower-challenges.md` Appendix) to justify *why*
  scalar amplitude, finite-prime flow, measured trace, generic de Branges positivity, and finite
  Jacobi positivity are insufficient — i.e. why the obstruction is where it is.

**The guardrail sentence** (the strongest honest claim available now):

> `[PROVABLE / SYNTHESIS]` Existing promoted results and experiments **locate** the RH-facing
> obstruction at a completed, source-built, faithful archimedean-polarized object. They do **not**
> construct that object or prove its index vanishes.

Any sentence stronger than this must first pass the source-built-object, faithful-index,
index-vanishing, fake-family-separation, and no-margin theorems (`07-theorems-and-lemmas-required.md`
Appendix). The transport face (`d log ξ` defect calculus) and the faithful-index face (source-built
`κ₋`) may be two faces of one theorem; that equivalence is itself open and should be stated as such.
