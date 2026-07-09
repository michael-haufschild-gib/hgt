# Cocycle shape rigidity and Γ-extremality of vertical type

- **ID:** cocycle-shape-rigidity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** reflection-cocycle lane (ReflectionCocycleClass/Curvature/Archimedean); INT-ORDER re-cut
- **Statement:** `[CONJECTURE]` Every ordinary Dirichlet series with finite abscissa and entire continuation has vertical-line exponential type ≤ π/2; equivalently, every reflection cocycle `h_F(s) = F(1−s)/F(s)` of such a carrier that is meromorphic of finite order is Selberg-shape (conductor × Γ-quotients), i.e. its reflection curvature lies in the finite trigamma-sum cone.

## Goal

The Selberg class **postulates** the split shape `Q^{2s−1}·∏ Γ(λⱼs+μⱼ)/Γ(λⱼ(1−s)+μ̄ⱼ)` of the
functional-equation factor as an axiom; the parent theory cannot ask whether that shape is forced.
Proving rigidity derives the axiom from the constraint side (the carrier's half-plane structure);
refuting it produces a non-Selberg carrier — an inhabitant of 𝓜⁺ invisible to the parent by
construction. Either outcome is knowledge the parent cannot state. Γ-extremality is the native
formulation: the archimedean generator is the growth-extremal point of the finite-abscissa class,
and the frequency lattice (the prime side) is what would enforce the bound — a constraint
(extremal/boundary condition), not a flow.

## Structure (established reductions)

1. **Hadamard split of the cocycle.** A finite-order meromorphic `h` factors as
   `e^{P}·(canonical-product quotient)` with `P` polynomial. The cocycle law `h(s)h(1−s)=1` and
   polynomially bounded modulus on vertical lines (realizability growth) force `deg P ≤ 1` —
   the exponent tier is exactly the conductor family `e^{a(s−1/2)+b}`.
   `[PROVED — Lean: cocycle_exponent_rigidity, CocycleExponentRigidity.lean]`
   Consequence: **all reflection curvature originates in the divisor part**; the divisor of `h_F`
   reads only the reflection-antisymmetric part of the divisor of `F` (FE-paired zeros cancel at
   equal order), which for classical members is the Γ-side lattice of trivial zeros.
2. **Divisor tier.** `[OPEN CORE]` Can the antisymmetric divisor of a realizable cocycle be
   anything other than finitely many affine arithmetic progressions on horizontal rays
   (Γ-divisors) plus finite sets (rational factors)? Trigamma-cone membership of the curvature is
   the analytic shadow of this divisor statement.
3. **Theta reformulation of the growth half.** `[SEARCH — frame; assembled here]`
   Ordinary Dirichlet series with `|aₙ| ≤ n^C` ⟷ `θ(x) = Σ aₙ e^{−nx}`, a **2πi-periodic**
   analytic function on `Re x > 0` with `|θ| ≤ poly(1/Re x)` on the whole half-plane, vanishing at
   `+∞`; `F` entire ⟺ `M[θ] = F·Γ` has at most simple poles, all in `ℤ≤0`. Rotating the defining
   contour with the half-plane poly bound gives Γ-matching decay with polynomial loss,
   `|M[θ](σ+it)| ≤ G(σ)|t|^{O(σ)}e^{−π|t|/2}`, **in the convergence region** `σ > C+1`.
4. **The exact residual gap.** `[OPEN CORE]` No a-priori order bound transfers that decay across
   the continuation: Phragmén–Lindelöf needs growth data on a left boundary that is exactly the
   unknown. Vertical type > π/2 for `F` ⟺ exponential growth of the *continued* `M[θ]` on left
   verticals. The one unexploited constraint is the 2πi-periodicity of `θ` (the frequency lattice).
5. **Frequency-lattice correction of INT-ORDER.** The load-bearing integrality is the **frequency
   lattice** `λₙ = log n` (⟹ monomials `e^{−nx}` ⟹ periodic θ ⟹ q-disk ⟹ Pólya–Carlson applies to
   integer *coefficients*), not coefficient integrality itself. General (non-lattice) Dirichlet
   series have no periodic theta and fall outside the whole mechanism.
6. **Saturation family.** `[CONJECTURE]` `aₙ = e^{i n^β}`, `0 < β < 1`: stationary phase gives
   radial oscillation `θ(x) ∼ x^{·}e^{ic x^{−β/(1−β)}}`; the Mellin phase of `e^{iu}` cancels the
   Γ-decay on one `t`-side, so the family should saturate type exactly π/2 (boundary-achieving,
   never exceeding). Witness at the flat end: `f(q) = e^{−(1+q)/(1−q)}` (Herglotz exponent),
   `aₙ = e^{−1}(Lₙ(2) − L_{n−1}(2))` bounded (Laguerre), `θ = O(x^N)` for all `N` radially, `F`
   entire with all-order-vanishing radial data.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

- Exponent tier: Lean module `CocycleExponentRigidity.lean` (reflection constraint kills even
  recentred degrees; vertical poly bound kills odd degree ≥ 3 through the `t^{d}`/`t^{d−1}`
  coefficient of the real part on a chosen vertical).
- Divisor tier: canonical-product quotients under the cocycle law + vertical growth; target — the
  divisor must be a finite union of affine progressions or the growth bound breaks.
- Type-π/2 tier: exploit periodicity of θ across the continuation (the only unused constraint), or
  break the conjecture by building exponential sector growth of the continued `M[θ]` compatible
  with periodicity + poly boundary bound. Pre-certify the `e^{i n^β}` saturation family numerically
  (mpmath) before any Lean work on it.

## Log
- 2026-07-09 — created in 1-in-progress; exponent tier delegated to Lean build

## Wave 2 — indicator lemma, product-closure attack, quantized types

7. **Finite order ⟹ vertical type 0.** `[LEMMA — provable via Levin indicator/proximate-order
   theory; [SEARCH]-grade proof, load-bearing placement]` A finite-abscissa carrier is bounded on
   a right half-plane, so its Phragmén–Lindelöf indicator satisfies `h(φ) ≤ 0` on `|φ| < π/2`;
   continuity of the (proximate-order) indicator forces `h(±π/2) ≤ 0`, and the vertical directions
   ARE `±π/2` asymptotically at every fixed abscissa. Hence: **entire + finite Hadamard order ⟹
   exponential vertical type 0 on every vertical line.** μ-superlinearity and every positive
   vertical type live exclusively in the infinite-Hadamard-order regime. (Retro-justifies the
   finite-order closures of the h=1 lane; supersedes the "type ≤ π/2 ceiling" framing — at finite
   order the ceiling is 0.)
8. **Product-closure attack kills the naive π/2 ceiling.** The class is closed under products
   (Dirichlet convolution keeps polynomial coefficients; entire × entire = entire), and vertical
   types add on the common growth side. So IF one type-π/2 member exists, its square has type π:
   no ceiling at π/2, and no two-point quantization {0, π/2}. Surviving form:
   `[CONJECTURE TYPE-QUANTIZATION]` vertical types of finite-abscissa entire carriers lie in
   `(π/2)·ℕ₀`, positive type only at infinite Hadamard order; the boundary-resonance quantum is
   the archimedean quarter-turn `arg i = π/2` (the Mellin phase of `e^{iu}` — the theta half-plane
   boundary ray — is the unique oscillation mechanism, and it produces exactly π/2 per factor).
   Rigidity alternative: NO positive-type member exists at all (full INT-ORDER-type conclusion for
   ALL polynomial coefficients).
9. **The decisive test object.** Everything now hinges on one classical-looking but (to this
   session) unresolved question: the continuation status of `Σ e^{i n^β} n^{−s}` (sharpest at
   β = 1/2). Saddle heuristics: entire with vertical type exactly π/2 on one t-side, hence
   infinite Hadamard order — OR not entire at all (obstructed continuation), which is evidence for
   full rigidity. Settle β = 1/2 first: the θ-function is `Σ e^{i√n − nx}`, a quadratic-saddle
   object with classical asymptotics. `[OPEN — next move]`

## Log (cont.)
- 2026-07-09 — wave 2: indicator lemma (finite order ⟹ vertical type 0); product-closure
  self-attack kills naive ceiling; TYPE-QUANTIZATION conjecture ((π/2)ℕ₀); decisive test =
  e^{i√n} series continuation. Lean follow-up queued: indicator lemma needs Levin theory
  (absent from mathlib — major build, queued behind CocycleExponentRigidity).

## Wave 3 — saturation family REFUTED; Herglotz obstruction; rigidity strengthened

10. **§6/§9 corrected by sharper reasoning (pre-computation).** For `aₙ = e^{i n^β}` the saddle of
    `i u^β − ux` sits at `arg u = (π/2)/(1−β) ≥ π` — never on the positive real axis. Half-line
    Poisson at β = 1/2: the k = 0 term contributes `i√π x^{−3/2} e^{−1/(4x)}` (exponentially
    SMALL, not oscillatory) plus a Dawson-type expansion in **half-integer powers** of `x`; the
    k ≠ 0 saddles `u_k = −1/(4(x+2πik)²)` are analytic at `x = 0`. Consequence: `Σ e^{i√n} n^{−s}`
    continues meromorphically with (at most) simple poles on the negative half-integer ray
    `s = −(2j+1)/2`, Γ-matched vertical growth with `μ` LINEAR of slope 2 (the ratio
    `|Γ(3/2−s)/Γ(s)| ~ |t|^{3/2−2σ}`), and NO positive vertical type. The family does NOT
    saturate π/2 — `[REFUTED]` as a type-π/2 witness; it is instead a degree-2-flavored,
    half-integer-pole object (worth its own study as a non-Selberg-pole-lattice carrier).
11. **The Herglotz obstruction — the mechanism behind full rigidity.** `[CONJECTURE, mechanism
    named]` Positive vertical type needs genuine radial boundary resonance `θ(x) ∼ e^{i c x^{−γ}}`
    (γ > 0) at the theta boundary point. On the q-disk this means `f(q) ∼ e^{iψ(q)}` with `Re ψ`
    blowing up radially at `q = 1` while `Im ψ` stays bounded below near the WHOLE circle
    (else Cauchy coefficients grow like `exp(c n^{γ/(γ+1)})` — infinite abscissa; saddle of the
    coefficient integral has strictly positive real part `∝ cos(π/(2(γ+1))) > 0`). But the
    Hilbert-transform (conjugate-function) coupling on the disk forces Re-blowup ⟷ Im-sign-change:
    the atom-at-1 Herglotz term `i c (1+q)/(1−q)` is purely decaying radially, and rotating it
    into a real radial phase (`c(1+q)/(1−q)`) breaks positivity (`Im ∼ cot(φ/2)` changes sign).
    So: **polynomial coefficients forbid radial boundary resonance** — the conjugate-function
    positivity is the constraint that locks every finite-abscissa carrier to Γ-matched (type-0)
    growth. Slow (log-speed) oscillation `θ ∼ x^{iα}` IS coefficient-realizable but produces a
    pole at `s = −iα` (off `ℤ≤0`) — the shifted-ζ family — coherent: oscillation speed ⟷ pole
    location; fast resonance ⟷ forbidden; entirety + poly coefficients ⟹ Γ-locked.
    `[OPEN CORE]` make the Herglotz obstruction a theorem: no `f` with poly-growth Taylor
    coefficients has `|f(r)| ≍ 1` and unbounded radial phase velocity `∂_r arg f(r) ≫ (1−r)^{−1}`
    at a boundary point — a conjugate-function/Zygmund-class statement at the seam between
    boundary behavior and coefficient growth.
12. Type-quantization (§8) is moot under 11: the conjectured spectrum collapses to `{0}` —
    Γ-EXTREMALITY in the strongest form: **the archimedean factor is not just extremal, it is the
    unique growth phase**; every deviation is carried by poles (divisor data), never by type.
    The two-tier Hadamard split (§1–§2) and this growth rigidity are now the SAME statement seen
    from cocycle and carrier sides.

## Log (cont. 2)
- 2026-07-09 — wave 3: e^{i n^β} family refuted as type witness (exp-small radial data,
  half-integer poles, μ slope 2); Herglotz/conjugate-function obstruction named as the rigidity
  mechanism; type spectrum conjecturally {0}. Numerical pre-cert target updated: verify the
  half-integer-pole structure of Σe^{i√n}n^{−s} (mpmath), NOT the dead saturation claim.

## Wave 4 — Borel–Carathéodory phase cap; the open core in final function-space form

13. **Radial phase cap.** `[THEOREM-candidate, proof sketched]` `f` analytic on 𝔻 with
    `|f| ≤ (1−|q|)^{−A}`; along a radius where `|f| ≥ (1−r)^{B}` (no exponential smallness) the
    argument variation is `O(log²(1/(1−r)))`: Jensen counts `≲ A log(1/(1−r))` zeros per dyadic
    disk `D(x, x/2)` (each contributing O(1) winding), and Borel–Carathéodory on the zero-free
    part (`Re log f ≤ A log` upper bound is exactly what B–C needs) caps `|arg|` by
    `O(log(1/(1−r)))` per scale. Fast radial resonance `e^{i c (1−r)^{−γ}}` is impossible at
    polynomially controlled modulus — for EVERY γ > 0.
14. **Tilted (subdominant) resonances are killed by the same global bound.** `e^{(−a+ic)/(1−q)}`
    (exp-small on the radius, spinning, would give intermediate vertical type `arctan`-graded):
    its `Re ψ = −a/2 − (c/2)cot(φ/2)` blows up POSITIVELY on one side of the circle — violating
    `|f| ≤ (1−|q|)^{−A}` outright. The Hilbert-transform coupling (Re-blowup ⟷ Im-sign-change)
    excludes every rotation of the atom; no coefficient asymptotics needed, the whole-circle
    polynomial bound suffices. This is the Herglotz obstruction (wave 3) in its correct global
    form.
15. **Open core, final function-space form.** `[OPEN CORE — T2]` `f` analytic on 𝔻,
    `|f| ≤ (1−|q|)^{−A}`, `θ(x) = f(e^{−x})`; ASSUME `M[θ]` continues with at most simple poles
    in `ℤ≤0`. Prove: `M[θ]` has vertical growth `O(e^{ε|t|})` for every ε > 0 (type 0) —
    equivalently `F = M[θ]/Γ` has vertical type 0. Strategy: `log⁺|f|` has the integrable boundary
    majorant `A·log(1/dist)` ⟹ Nevanlinna-type harmonic-majorant control of `f` in sectors;
    rotated contours + the majorant replace the missing left-boundary data that Phragmén–Lindelöf
    wanted. This single statement now carries: shape rigidity's growth half, Γ-extremality,
    INT-ORDER for all polynomial coefficients, and the h=1 infinite-order cell.

## Log (cont. 3)
- 2026-07-09 — wave 4: B–C phase cap (theorem-candidate); tilted resonances globally excluded;
  P–L gap replaced by concrete disk statement T2 (Nevanlinna majorant → Mellin type 0).

## Wave 5 — T2 is the loud-cell wall in disk coordinates (the trade that matters)

16. **Attack on T2 (attempted inverse construction).** A counterexample needs an entire `F`,
    almost periodic with spectrum `{log n}` on one right vertical (this is what 2πi-periodicity of
    the inverted θ demands), polynomially bounded there with Γ-matched exactness, exponentially
    large on left verticals — i.e. precisely a **loud carrier** of the h=1 infinite-order cell
    (goldilocks lane wave 4: "all lower-bound machinery exists, no upper mechanism does").
17. **The equivalence and the trade.** `[BRIDGE — internal, load-bearing]` T2 ⟺ the loud-cell
    upper-bound problem. But the q-disk change of variables has ABSORBED the almost-periodicity:
    T2's hypotheses mention only `f` analytic on 𝔻 with `|f| ≤ (1−|q|)^{−A}` and the pole
    location of `M[θ]` — plain single-variable function theory, no arithmetic, no a.p. structure,
    no lines. The intractable "upper bound on strip loudness from a.p. flank data" became a
    classical disk statement. Forward: prove T2 with disk tools (harmonic majorants, Nevanlinna
    theory, the B–C phase cap of wave 4 extended to tangential approach regions), or build the
    counterexample `f` with disk tools — either resolves the h=1 infinite-order cell, INT-ORDER
    (all polynomial coefficients), Γ-extremality, and the growth half of shape rigidity at once.

## Log (cont. 4)
- 2026-07-09 — wave 5: T2 ⟺ loud-cell upper bound; a.p.-on-lines traded for
  analyticity-on-disk. The four open cores of the lane are now ONE disk statement.

## Log (cont. 5)
- 2026-07-09 — exponent tier LANDED in Lean: `CocycleExponentRigidity.lean` (420 lines, 5 public
  theorems: shifted_coeff_even_eq_zero, exists_vertical_re_growth, cocycle_exponent_rigidity,
  cocycle_exponent_curvature_zero, cocycle_exponent_eq_conductor_form). Verified: lake build
  8582 jobs green; #print axioms = [propext, Classical.choice, Quot.sound] for all five; formal
  lint passed; index regenerated; module wired into RHTower umbrella. §1 of Structure is now
  machine-checked.

## Wave 6 — stolz-bc jaw executed: interface theorem, pure-class no-go, superposition closure

18. **The sharp conditional interface.** `[LEMMA — Levin-standard proof; the precise residue]`
    entire + bounded on a right half-plane + finite proximate order ⟹ vertical type 0 at every
    abscissa (indicator ≤ 0 on the open right directions, continuity pins h(±π/2) ≤ 0, and the
    vertical directions ARE ±π/2). T2 is exactly "remove the order hypothesis using the disk."
19. **Pure-class no-go for T2 (transfer of the goldilocks wave-3 verdict).** `[PROVED-modulo-
    Arakelyan details]` E = {Re s ≥ σ₀} ∪ {Re s = −1} has the same two-channel Arakelyan geometry
    as the wave-3 set (sphere complement: two strips joined at ∞, connected, locally connected),
    so tangential approximation produces an entire F, bounded on the right half-plane, with
    `Re log F ≥ |t|` on the line Re s = −1: **two-region growth data alone cannot prove T2**; any
    proof must consume disk-analyticity / one-sided spectrum, not just entirety + boundedness.
20. **Boundary-rotation tautology.** Rotating the Mellin ray to arg x = ±π/2 lands on the
    boundary Fourier series of f and reproduces `F·Γ` identically (the `e^{iπs/2}` from the ray
    cancels against `(im)^{−s}`); the negative-frequency side is empty. One-sidedness is the
    binding clause — rotation alone extracts nothing new past the boundary.
21. **Superposition closure — the type-0-closed class.** `[THEOREM-candidate, sketched]`
    Coefficient profiles `aₙ = Ĝ-superpositions ∫ n^{iξ} G(ξ)dξ` with `G` analytic and decaying
    in every horizontal strip give `F(s) = ∫ G(ξ) ζ(s−iξ) dξ`: entire (pole line contour-shifts
    away) with polynomial verticals — each shifted ζ has μ linear (χ-factor), and superposition
    preserves it. The Knill almost-periodic class is an instance. So every "coefficient recipe"
    built from analytic character superpositions stays at type 0; a T2 counterexample needs
    coefficients OUTSIDE every such superposition while keeping entirety — the same exclusion the
    disk formulation states as: no Korenblum-bounded f does fast boundary resonance.
22. Lean brick landed for the program: `ThetaHalfPlaneBound.lean` — summability + the envelope
    `‖θ(x)‖ ≤ 3·A!·2^A·C/(Re x)^{A+1}` (uniform in arg x), the growth input for every future
    Mellin-rotation formalization. (Verification evidence in Log.)

## Log (cont. 6)
- 2026-07-09 — wave 6 (rng: stolz-bc): interface theorem isolated; pure-class no-go transferred
  (Arakelyan two-channel); boundary rotation shown tautological (one-sidedness binding);
  superposition-closure instances unified. Lean: ThetaHalfPlaneBound.lean written by hand.

## Log (cont. 7)
- 2026-07-09 — ThetaHalfPlaneBound.lean VERIFIED: standalone compile clean (zero warnings),
  umbrella build 9094 jobs green, all 8 declarations axiom-clean [propext, Classical.choice,
  Quot.sound], formal lint passed, index regenerated, in RHTower umbrella.
