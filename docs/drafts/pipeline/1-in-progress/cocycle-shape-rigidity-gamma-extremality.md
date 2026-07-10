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

## Wave 7 — zero-bridge killed; order/type decoupling; the Borel–Ritt monster; keystone re-cut

23. **The zero-counting bridge FAILS at its first arrow — do not rebuild.** The chain was: F loud
    at σ₀ < 0 ⟹ θ oscillates at the boundary ⟹ zeros violate Korenblum density. But the loudness
    lives on the CONTINUED M[θ], which is not an integral of θ; the only unconditional link
    F → f is Mellin inversion on a right line, where F is tame; continued values reach f only
    through analytic-continuation uniqueness, which has no quantitative form (wave-6 Nevanlinna
    verdict). "Loud ⟹ resonant" is the P–L gap renamed. The wave-4 apparatus constrains the
    resonance direction only. Residue kept: the divisor stays the curvature carrier
    (shape-rigidity side); as a T2 tool it waits on the missing arrow.
24. **Order/type decoupling.** The σ-aspect (Hadamard order; the values F(−k) = ±k!·c_k = the
    radial JET of θ at 0) and the t-aspect (vertical type; boundary resonance) are separate
    channels. T2 constrains ONLY the t-aspect. Symmetric carriers (h=1 cell) have their σ-aspect
    killed by F(s)=F(1−s) + flank boundedness, so T2 ⟹ h=1 rigidity in full — unchanged. But for
    UNSYMMETRIC carriers the σ-aspect is genuinely free:
25. **The Borel–Ritt monster — INT-ORDER is FALSE without integrality.** `[PROVED-modulo-writeup]`
    Take any formal series Σc_k x^k (integer powers), e.g. c_k = e^{e^k}/k!. Borel–Ritt on the
    sector |arg x| < π/2 + ε gives θ̃ asymptotic to it, uniformly, bounded; multiply by (1+x)^{−2}
    for decay. Periodize: θ(x) = Σ_{j∈ℤ} θ̃(x + 2πij) — 2πi-periodic, analytic on Re x > 0,
    BOUNDED on the half-plane (the lattice sum converges by the |x|^{−2} decay), vanishing at
    +∞; the j ≠ 0 part is analytic AT x = 0 (each translate sits at arg ≈ π/2 < π/2 + ε) with
    geometrically small Taylor coefficients — no cancellation against the prescribed jet. Fourier
    coefficients: one-sided, bounded ⟹ F = Σaₙn^{−s} with finite abscissa. Full integer-power
    radial asymptotic (sector-uniform) ⟹ M[θ] poles ⊂ ℤ≤0 simple ⟹ F ENTIRE, and the rotated
    remainder bounds give vertical type 0 — but F(−k) ≈ e^{e^k}: INFINITE Hadamard order.
    Consequences: (i) "finite abscissa + entire ⟹ finite order" is FALSE for bounded complex
    coefficients — the σ-aspect jet is a free parameter; (ii) the old heuristic "entirety forces
    coefficient regularity capping growth" is wrong for ORDER and right (conjecturally) only for
    TYPE; (iii) T2 and Γ-extremality are untouched (the monster is type 0); (iv) the h=1 cell is
    untouched (needs symmetry, which the monster breaks maximally).
26. **The keystone re-cut: jet quantization.** `[CONJECTURE JET-QUANT]` For INTEGER bounded
    coefficients the Borel–Ritt freedom dies because the coefficients are quantized — the jet
    cannot be prescribed continuously. Via Pólya–Carlson: integer f is rational (⟹ F a Hurwitz
    combination, finite order — the known world) or has a natural boundary; conjecture: **a
    natural boundary is incompatible with a full integer-power radial asymptotic at q = 1** (some
    half-power / log / log-periodic term always intrudes — as in Σq^{n²} (x^{−1/2} term) and
    Σq^{2^n} (log-periodic oscillation)). JET-QUANT ⟹ integer INT-ORDER holds in full (entire
    integer cases are exactly the rational-f, finite-order world). This is Pólya–Carlson in the
    JET variable — the branch-native successor of INT-ORDER, now correctly scoped after 25.

## Log (cont. 8)
- 2026-07-09 — wave 7: zero-bridge self-attacked and killed (first arrow = P–L gap renamed);
  order/type channels decoupled; Borel–Ritt periodization monster constructed (bounded
  coefficients, entire, infinite order, type 0) — INT-ORDER false without integrality; keystone
  re-cut as JET-QUANT. Lean: Borel–Ritt/sector-asymptotics absent from mathlib — formalization
  of wave-7 queued as a named major target (AsymptoticExpansionSector + periodization), behind
  the T2 program; no small brick this wave moves a quantifier.

## Wave 8 — JET-QUANT refuted; the integer world stratified; Cobham-flavored rigidity

27. **0/1 stratum closed by Landau `[SEARCH]`.** For gap sets Λ ⊆ ℕ, `M[Σe^{−λx}] = Γ·L_Λ` with
    `L_Λ(s) = Σ_{m∈Λ} m^{−s}` — nonnegative coefficients, so Landau's theorem places a genuine
    singularity at the real abscissa: an infinite 0/1 series is NEVER entire. Geometric gaps show
    the intrusion explicitly: `Σq^{2^n}` gives `Γ(s)/(1−2^{−s})`, pole lattice `2πiℤ/log 2`.
28. **JET-QUANT is REFUTED.** `f = Σ(−1)^n q^{n²}`: Fabry (gaps `n²/n → ∞`) gives a natural
    boundary on `|q|=1`; yet `F(s) = Σ(−1)^n n^{−2s} = −η(2s)` is ENTIRE of finite order, with a
    full integer-power radial expansion. A natural boundary does not obstruct entirety — the
    wave-7 intrusion conjecture dies. Signs are everything: positivity (27) was the only
    obstruction there.
29. **PERIODIC-DICHOTOMY refuted in the same stroke.** `aₙ = (−1)^n + (alternating on squares)`
    is bounded-integer, NOT eventually periodic, with `F = −η(s) − η(2s)` entire. The escape:
    periodic data transported along monomial pushforwards `k ↦ k^d` (and, more generally,
    alternating signs along polynomial images `k ↦ P(k)`, entire by Boole summation). All such
    combinations have order ≤ 1.
30. **Where the intrusion mechanism SURVIVES: self-similar (automatic) structure.** Thue–Morse
    type 2-substitution relations force `(1 − 2^{·−s})`-style denominators ⟹ candidate pole
    lattices `ρ + 2πiℤ/log 2`. Geometric-support integer series are never entire (a nontrivial
    integer power series in `w = 2^{−s}` entire in `s` needs radius ∞ ⟹ coefficients → 0 ⟹
    finite). `[CONJECTURE AUTOMATIC-COBHAM-RIGIDITY]`: **an automatic bounded-integer sequence
    whose Dirichlet series continues to an entire function is eventually periodic** — entirety
    kills the substitution poles only in the degenerate (periodic) case; a Cobham-flavored
    rigidity: the pole lattice of the substitution plays the role of the second base.
31. **The keystone, wave-8 form.** `[CONJECTURE INT-ORDER ≤ 1]` integer polynomial-size
    coefficients + finite abscissa + entire ⟹ Hadamard order ≤ 1. Evidence: the entire visible
    integer world (periodic/η/Hurwitz data, monomial pushforwards, alternating polynomial images)
    sits at order ≤ 1; positivity blocks 0/1; substitution structure blocks automatic non-periodic
    (conj. 30); Borel–Ritt jet freedom needs continuous tuning (wave 7). `[OPEN CORE — ARITHMETIC
    LATTICE STRUCTURE]`: is every bounded-integer entire Dirichlet series a finite combination of
    periodic data along polynomial pushforwards? The structure theorem would prove the
    quantization and give integer INT-ORDER in the corrected (≤ 1) form.
32. **Lean target pinned (absent from tree and mathlib; tree's "Landau positivity" is the
    real-axis Euler-factor shadow, not the theorem):** `landau_summability_transfer` — for
    `0 ≤ aₙ`, `LSeriesSummable a σ₁`, and `G` analytic on `ball(σ₁, r)` agreeing with the series
    on the convergent overlap: summability transfers to every real `σ > σ₁ − r`. Proof core:
    `LSeries_iteratedDeriv` (in mathlib) + Taylor-coefficient sign pattern + Tonelli
    rearrangement of the nonnegative double series. This is the positivity engine that formally
    closes stratum 27 and is reusable at every seam positivity argument.

## Log (cont. 9)
- 2026-07-10 — wave 8: JET-QUANT and PERIODIC-DICHOTOMY both refuted by explicit integer
  examples (alternating quadratic partial theta; pushforward escape); 0/1 stratum = Landau;
  automatic stratum = substitution pole lattices [CONJECTURE Cobham-rigidity]; keystone re-cut to
  INT-ORDER ≤ 1 + arithmetic-lattice structure theorem. Lean next: landau_summability_transfer.

## Wave 9 — automatic/order conjectures refuted by the Thue--Morse Mellin carrier

33. **AUTOMATIC-COBHAM-RIGIDITY is false.** `[SEARCH + PROVED RECHECK]` Let
    `epsilon_n=(-1)^{s_2(n)}`. The shifted Thue--Morse Dirichlet series
    `T(s)=sum_{n>=0} epsilon_n/(n+1)^s` is entire, although `epsilon` is 2-automatic and not
    eventually periodic. The continuation is classical (Allouche--Cohen, 1985). The mechanism is
    the exact generating product
    `sum epsilon_n q^n=prod_{k>=0}(1-q^{2^k})`: on `q=e^{-x}`, every finite initial product supplies
    one more power of `x`, so the kernel is flat to all algebraic orders at `x=0`. Substitution does
    not force a pole lattice when its Prouhet cancellations accumulate to infinite radial order.
34. **INT-ORDER <= 1 is false.** `[PROVED HERE]` The same entire Dirichlet series has exact Hadamard
    order `2` and exact type `(log 2)/2`. Writing
    `phi(x)=e^{-x}prod_{k>=0}(1-e^{-2^k x})`, two-sided product bounds give
    `log phi(e^{-y})=-y^2/(2 log 2)+O(y)`. Its Mellin transform therefore has
    `log M(r)=((log 2)/2)r^2+o(r^2)` along the negative real direction; division by `Gamma(s)` changes
    only the `O(r log r)` term. Complete proof:
    `../2-fully-proven/new/thue-morse-entire-dirichlet-order-two.md`.
35. **Corrected keystone.** Integrality, boundedness, and finite-state self-similarity are all too
    soft to cap Hadamard order. The surviving source question must include multiplicativity/Euler
    compatibility: `[OPEN CORE]` can a nonzero bounded **multiplicative** integer sequence have an
    ordinary generating function with infinite radial Prouhet flatness at `q=1` while its Dirichlet
    series continues entire? An order-one theorem is useful only if that flatness obstruction is
    derived from the Euler constraint, not assumed as finite order.

## Log (cont. 10)
- 2026-07-10 — wave 9: refuted AUTOMATIC-COBHAM-RIGIDITY and INT-ORDER <= 1 by the shifted
  Thue--Morse Dirichlet series. Entirety is classical and graded SEARCH; the exact order `2`, exact
  type `(log 2)/2`, and the two-sided radial-flatness proof are recorded in the new stage-2 card.
  Keystone moved to the multiplicative obstruction to infinite radial Prouhet cancellation.

## Log (cont. 10)
- 2026-07-10 — `LandauSummabilityTransfer.lean` LANDED (hand-written, 2 fix cycles): verified
  standalone clean zero warnings, umbrella build 9108 jobs green, both public theorems
  [propext, Classical.choice, Quot.sound], formal lint passed, index regenerated. During the
  build the `R > 1` hypothesis turned out redundant (the case split derives it) and was removed —
  the formalization strengthened the statement. §32's pinned target is machine-checked; the 0/1
  stratum (§27) is now formally closed via `landau_entire_summable` + divergence at σ = 0.

## Wave 9 — Thue–Morse refutes Cobham-rigidity; integer sublane CLOSED; the two machines compose

33. **AUTOMATIC-COBHAM-RIGIDITY is REFUTED — by Thue–Morse itself `[SEARCH]`.** The signed
    kernel relations `t(2n) = t(n)`, `t(2n+1) = −t(n)` make the parity split's principal terms
    CANCEL: `F(s) = 1 − Σ_{j≥1} binom(−s,j) 2^{−s−j} F(s+j)` — no `(1−2^{−s}B)⁻¹` inversion, no
    pole lattice; iterating continues `F` to an ENTIRE function. Thue–Morse is 2-automatic,
    non-periodic, ±1. The intrusion mechanism (§30) reads the UNSIGNED kernel matrix; the signed
    linear representation can degenerate the spectrum to `{0}`. §31's structure conjecture dies
    with it (Thue–Morse lies outside the pushforward-periodic algebra; non-regular escapes such
    as §29's exist too).
34. **Integer sublane CLOSED — verdict.** Every finer-than-positivity conjecture of waves 7–8
    (JET-QUANT, PERIODIC-DICHOTOMY, COBHAM-RIGIDITY, the lattice structure core) died to explicit
    classical-adjacent examples within one attack each: this terrain is the automatic/regular
    Dirichlet series literature — left of the wall. What the branch keeps: **positivity is the
    single theorem-grade entirety obstruction** (Landau — machine-checked here), INT-ORDER ≤ 1
    stays as background conjecture only. Do not re-enter this sublane.
35. **Divisor-tier no-go (counting cannot close it).** Two-sided polynomial vertical bounds +
    finite order give only `O(log T)` divisor points per dyadic box — but sparse VERTICAL
    divisors (zeros at `σ₀ + i2^k`, poles mirrored) have Γ-level box counts while being no
    horizontal progression. The divisor tier is carrier-forced, like T2; pure growth/counting
    arguments can never force the Γ-shape.
36. **The composition Q-COC — the two banked machines finally meet.** `[TARGET — provable-looking;
    Lean generalization pinned]` In `quiet_crossing_conductor_support` the FE datum enters ONLY
    through its size `H(M) = CJ·Q₀^{1+2M}` on the shifted flank `Re s = −M` (tree line ~120).
    Generalize the datum to an abstract cocycle `h` with flank bound
    `‖h(−M+it)‖ ≤ H(M)·(2+|t|)^m` (the `(2+|t|)^m` absorbed into the quiet budget
    `q_k = o(T_k^{2−m})`): conclusion `‖aₙ‖ ≲ H(M)·(n−½)^{1−M}`, i.e.
    **support radius of the carrier = `limsup H(M)^{1/(M−1)}` = exponential of the cocycle's
    flank-growth rate.** Consistency: `H = Q₀^{1+2M}` recovers support `≤ Q₀²`; Γ-data
    (`H ~ e^{M log M}`) gives no bound — exactly why completed L-functions have infinite support.
37. **Consequence: the divisor tier closes conditionally.** A cocycle with sparse-vertical
    divisor + conductor exponent has `H(M) ≤ e^{aM}·O(1)` ⟹ support radius `≤ e^a` FINITE ⟹ `F`
    a Dirichlet polynomial ⟹ (banked degree-0 classification, machine-checked) its cocycle is a
    pure conductor datum — whose divisor is NOT sparse-vertical: CONTRADICTION. So, conditional
    on one quiet height sequence: **realizable finite-order poly-vertical cocycles with
    subexponential-beyond-conductor flank growth are exactly the conductor data; every
    non-conductor divisor forces Γ-scale (`e^{cM log M}`) flank growth.** The Selberg degree
    dichotomy (degree 0 vs Γ-degree ≥ 1) is DERIVED from the quiet-crossing machine, not
    postulated — the shape axiom's first tier falls out of the composition. Remaining shape
    freedom = the realizable ladder of flank-growth profiles between `e^{aM}` and Γ-scale.

## Log (cont. 11)
- 2026-07-10 — wave 9: Cobham-rigidity refuted (Thue–Morse signed cancellation); integer sublane
  closed with verdict "positivity is the only theorem-grade obstruction"; divisor-tier counting
  no-go; Q-COC composition discovered — support radius = exp(flank rate); degree dichotomy
  derived conditionally. Next execution: generalize QuietCrossingConductor.lean to abstract
  flank datum H(M) (Q-COC), per §36.

## Wave 10 — Q-COC corrected and promoted as a one-sided growth-to-support theorem

38. **The proposed equality is false as stated.** A valid flank majorant `H(M)` can be inflated
    arbitrarily, and the zero carrier satisfies majorants of every exponential rate. Therefore
    `support radius = limsup H(M)^(1/(M-1))` is not an invariant statement. The surviving theorem is
    one-sided. The fixed-knot proof first gives the scale `n-1/2`; varying the knot width removes
    that artifact exactly.
39. **Q-COC `[PROVED HERE]`.** If the quiet-crossing contour has a uniform left-rectangle bound
    `|F(s)|<=H(M)` at depth `M`, then
    `|a_n/2|<=2 H(M)(n-1/2)^(1-M)`. More generally, the knots `n+delta,n,n-delta` isolate
    `delta*a_n` and replace the left-edge scale by `n-delta`. Hence an eventual envelope
    `H(M)<=C R^M` kills every coefficient with `R<n`; equivalently `a_n!=0` implies the exact bound
    `n<=R`. Constant flank growth recovers degree zero; `H(M)=C_J B Q_0^(1+2M)` recovers support
    `n<=Q_0^2`; Gamma-scale growth has infinite geometric radius and correctly escapes. Complete proof:
    `../2-fully-proven/new/quiet-flank-growth-support-radius.md`.
40. **Intrinsic version and remaining core.** Minimize `R` over all admissible geometric flank
    envelopes before treating it as a cocycle invariant. Even then the theorem gives only an upper
    support bound. The RH-facing missing arrow is unchanged but sharper: manufacture the quiet
    sequence (or equivalent contour-smallness) for the target completed carrier, or derive finite
    intrinsic flank radius from a non-Gamma divisor constraint.

## Log (cont. 12)
- 2026-07-10 — wave 10: attacked and removed the non-invariant equality in Q-COC; proved the
  arbitrary-flank contour estimate, then varied the Perron knot width to obtain the exact support
  bound `n<=R`; formalized the reusable ratio-test/Prop-interface endgame in
  `QuietFlankGrowth.lean`. No umbrella build was run.

41. **Variable-knot source formalized.** `[PROVED Lean]` `VariablePerronKink.lean` constructs
    `K_{n,delta}`, proves its zeros at `0,-1`, the entire regularization, the uniform norm bound, and
    the exact smoothed identity `secondDifference = delta*a_n`. The fixed kernel is definitionally
    the `delta=1/2` specialization. The only remaining Q-COC formal layer is the generic rectangle
    producer from an abstract left-flank envelope to `HasVariableQuietFlankCoefficientBound`.

## Wave 11 — boundary charge replaces uniform quietness

42. **The common-height quantifier was spurious.** `[PROVED HERE]` The rectangle proof only needs,
    for each depth `M` and knot width `delta`, some exhaustion along which the two horizontal edge
    integrals vanish. It never compares exhaustions at different depths. Thus `exists T, forall M`
    is replaced by the strictly weaker proof interface `forall M,delta, exists T_{M,delta}`.
43. **Native object: normalized Perron boundary charge.** `[PROVED HERE + Lean]` At `(M,delta)`,
    package right-edge convergence, vanishing top/bottom charges, and a left charge bounded by
    `2*pi*H(M)*(n-delta)^(1-M)`. Cauchy's rectangle identity gives the coefficient Prop directly;
    if `H(M)<=C*R^M`, then `a_n!=0` implies the exact support bound `n<=R`. Complete proof:
    `../2-fully-proven/new/perron-boundary-charge-support.md`; formal module:
    `formal/GaloisForLFunctions/RHTower/PerronBoundaryCharge.lean`.
44. **Strip-mass producer.** `[PROVED Lean]` Integrability of the right edge, integrability in the
    height variable of the top-plus-bottom edge norms, and an L1 left-edge bound produce the
    boundary charge by choosing `T_k in [k,k+1]` where the horizontal mass tends to zero. Finite
    two-dimensional strip mass is sufficient by Tonelli. Uniform quietness is now only one
    producer, not the theorem's hypothesis.
45. **Next invariant.** `[PROVED HERE + Lean]` The kernel-dependent charge factors through two
    coefficient-independent carrier quantities: geometric negative-line `L2` energy and finite
    weighted horizontal mass. They dominate every `E_{n,delta}`, manufacture the quiet exhaustion,
    and preserve the exact support radius. Exact common-source cross-line coherence does produce the
    negative energy, but wave 13 proves that combining it with horizontal mass forces finite
    Dirichlet support. Thus the infinite-support target needs a defect-bearing seam law, not exact
    trace identification.

## Log (cont. 13)
- 2026-07-10 — wave 11: formalized the exact variable Perron integral; replaced uniform
  quiet-crossing by depth-dependent boundary charge; composed charge through the coefficient Prop
  to exact support; formalized the continuous-integrable strip-mass producer. The remaining object
  is a coefficient-independent weighted mass of the carrier. No umbrella build.

## Wave 12 — carrier masses replace kernel-dependent escape

46. **Left growth is a carrier invariant.** `[PROVED HERE + Lean]` The universal estimate
    `|E_{n,delta}(-M+it)| <= 4(n-delta)^(1-M)/(1+t^2)` shows that the quantitative contour datum is
    exactly the coefficient-independent mass
    `A_M(F)=integral |F(-M+it)|/(1+t^2)dt`.
47. **Hilbert-source producer.** `[PROVED HERE + Lean]` Vertical `L2` energy `B_M(F)` gives
    `A_M(F)<=sqrt(pi)B_M(F)` by Holder. A geometric envelope for `B_M` therefore yields the same
    exact arithmetic support radius.
48. **Horizontal mass removes quiet heights.** `[PROVED HERE + Lean]` An explicit uniform strip
    envelope gives quadratic height decay for `E_{n,delta}`. Finite weighted horizontal carrier
    mass selects the necessary height exhaustion; absolute Dirichlet convergence supplies the right
    edge automatically.
49. **Coefficient-independent capstone.** `[PROVED HERE + Lean]`
    `coefficient_index_le_exact_flank_radius_of_carrierL2StripMass` consumes only geometric
    negative-line `L2` energy and finite weighted horizontal carrier mass, then proves
    `a_n != 0 -> n<=R`.

## Log (cont. 14)
- 2026-07-10 — wave 12: separated Perron growth from escape; formalized carrier-only flank and
  horizontal masses, the L2-to-L1 producer, automatic right convergence, and the exact-support
  capstone. The remaining source theorem is now coefficient-free. No umbrella build.

## Wave 13 — exact source/carrier coherence is too rigid

50. **The physical Sonin gap produces every negative source moment.** `[PROVED HERE + Lean]` If
    `f` lies in the even Sonin carrier at cutoff `q>0`, then `g=logEvenUnitary(f)` vanishes almost
    everywhere below `log q`. Hence
    `||exp(-Mt)g||_2 <= q^(-M)||g||_2`. The normalized Fourier--Mellin unitary preserves this bound.
51. **Native seam constraint.** `[PROVED Lean]` `HasCoherentNegativeMellinTraces F g tau` says that
    every negative integer line of one analytic `F` agrees almost everywhere with the normalized
    transform of `exp(-Mt)g`. This Prop discharges `HasPerronCarrierFlankL2Energy` with exact radius
    `q^(-1)`.
52. **Cross-support transfer.** `[PROVED HERE + Lean]` Coherence plus finite horizontal carrier mass
    forces `a_n!=0 -> n<=q^(-1)` for every coefficient in the right-half-plane Dirichlet expansion.
    Therefore the coefficient support is finite at every `q>0`; if `q>1`, analytic continuation
    forces `F=0` identically.
53. **Naive weld refuted.** `[FALSIFIED]` A nonzero infinite-support Dirichlet carrier can retain
    finite horizontal mass while every negative line is exactly the weighted transform of one
    lower-supported Sonin source. The formal theorem
    `not_coherent_of_infinite_coefficient_support` rules this out for every positive cutoff.
54. **Defect law selected.** `[PROVED HERE + Lean]` Wave 14 constructs an additive `L2` cross-line
    defect and proves that its coefficient-indexed Perron pairings, rather than its full norm,
    carry the infinite arithmetic tail. Complete obstruction proof:
    `../2-fully-proven/new/sonin-perron-support-transfer.md`.

## Log (cont. 15)

- 2026-07-10 — wave 13: formalized logarithmic lower support, negative Mellin source moments,
  normalized traces, and cross-line coherence; composed them with coefficient-independent Perron
  mass. The resulting reciprocal support theorem refutes exact coherence for every infinite-support
  carrier. Targeted module build only; no umbrella build.

## Wave 14 — the cross-line seam has arithmetic coordinates

55. **Additive seam object.** `[PROVED Lean]` `HasCrossLineMellinDefect F g tau Delta` replaces exact
    trace equality by `F(-M+it)=T_M(g)(t)+Delta_M(t)` almost everywhere. Exact coherence is the
    zero-defect specialization.
56. **Exact boundary transport.** `[PROVED HERE + Lean]` If the left integrand is integrable and
    the horizontal edges escape, the full negative-line Perron integral equals the full right-line
    integral. The variable Perron kernel is an `L2` test vector with norm at most
    `4*sqrt(pi)*(n-delta)^(1-M)`.
57. **Coefficient charge splitting.** `[PROVED HERE + Lean]` At every escaping depth,
    `delta*a_n = sourceCharge_(M,n,delta) + seamResidue_(M,n,delta)`. If
    `q^(-1)<n-delta`, the source charge tends to zero geometrically.
58. **Arithmetic tail recovery.** `[PROVED HERE + Lean]` The knot-normalized seam coordinate
    `delta^(-1)*seamResidue` converges to `a_n`. A nonzero coefficient gives an eventually nonzero
    seam witness. Any two admissible knot widths yield asymptotically equal coordinates.
59. **Defect choice was spurious.** `[PROVED HERE + Lean]` Wave 15 proves that the additive `L2`
    seam is unique and canonically constructed from the carrier line; existing flank energy
    discharges its eventual existence. Complete proof:
    `../2-fully-proven/new/perron-mellin-seam-residue.md`.

## Log (cont. 16)

- 2026-07-10 — wave 14: replaced the falsified exact-coherence weld by an additive seam defect;
  formalized exact left/right boundary transport, source-charge decay, coefficient recovery,
  persistent seam witnesses, and knot-width invariance. Targeted module build only; no umbrella
  build.

## Wave 15 — the seam is canonical and source-gauge invariant

60. **Local uniqueness.** `[PROVED HERE + Lean]` At a fixed depth and source trace, two additive
    `L2` seam defects satisfying the same a.e. decomposition are equal as `L2` classes. The defect is
    forced, not selected.
61. **Canonical construction.** `[PROVED HERE + Lean]` Whenever `F(-M+i·)` lies in `L2`, define
    `Delta_M^can=[F(-M+i·)]-T_M(g)`. The existing `HasPerronCarrierFlankL2Energy` Prop plus
    differentiability supplies this membership eventually, so `HasEventuallyCrossLineMellinDefect`
    is discharged internally.
62. **Hypothesis-free seam recovery.** `[PROVED HERE + Lean]` The normalized Perron coordinate of
    `Delta^can` converges to `a_n` beyond the reciprocal source cutoff using only flank energy,
    horizontal mass, and the right Dirichlet identity. No defect/coherence Prop remains.
63. **Source-gauge invariance.** `[PROVED HERE + Lean]` Canonical defects relative to any two Sonin
    sources give asymptotically equal coefficient coordinates beyond both source radii. The `L2`
    representatives change; the arithmetic seam class does not.
64. **Completed/raw audit.** `[OPEN CORE]` The real target mismatch is now exposed. `xi` has the
    archimedean vertical decay but its right edge is `archFactor*LSeries`; raw eta has the arithmetic
    edge but no established deep-line mass. Construct an archimedean-completed Perron coordinate
    that extracts an explicit coefficient plus computable Gamma/boundary charge. Complete proof:
    `../2-fully-proven/new/canonical-perron-mellin-seam.md`.

## Log (cont. 17)

- 2026-07-10 — wave 15: weakened all-depth defects to the eventual interface, proved local
  uniqueness, constructed the canonical defect from flank energy, eliminated the defect Prop from
  coefficient recovery, and proved two-source gauge invariance. Targeted module build only; no
  umbrella build.

## Wave 16 — completed coefficient extraction and the scalar decompletion wall

65. **Second-order balance fails.** `[FALSIFIED]` Multiplying the existing Perron kernel by the
    boundary multiplier `s-1` lowers vertical decay from `O(|t|^-2)` to `O(|t|^-1)`. The current
    Bochner-integral Perron interface cannot consume it.
66. **Minimal third-order repair.** `[PROVED HERE + Lean]` The balanced physical weight
    `max(1-u,0)(3u-1)/2` has Mellin transform `(s-1)/(s(s+1)(s+2))`. Four symmetric knots at
    `n+-delta/2,n+-3delta/2` annihilate every off-target quadratic contribution and extract exactly
    `3delta^2*a_n/4` for `0<delta<2/3`.
67. **Entire boundary decompletion.** `[PROVED HERE + Lean]`
    `D_infty=2*dslope(Gamma_R^(-1),0)` is entire and satisfies
    `archFactor*D_infty=s-1` off the Gamma divisor. It composes directly with a completed Dirichlet
    expansion; no seam-defect or coherence Prop is introduced.
68. **Concrete xi charge.** `[PROVED HERE + Lean]` The completed zeta carrier paired with
    `D_infty*E3` has exact right-edge charge `3delta^2/4` at every coefficient index.
69. **Scalar decompletion obstruction.** `[PROVED HERE + Lean]` Any pointwise scalar probe solving
    `archFactor*K=s-1` is forced to equal `D_infty`, and
    `xi*D_infty=(s-1)zeta`. Exact scalar extraction cancels the Gamma decay. Additional polynomial
    smoothing can repair integrability but cannot preserve completed-carrier flank mass. Complete
    proof: `../2-fully-proven/new/archimedean-balanced-third-perron.md`.
70. **Non-diagonal frontier.** `[OPEN CORE]` The next completed extractor must couple the
    archimedean and finite-prime variables non-diagonally, or prove raw pole-cancelled carrier mass
    by another mechanism. Pointwise scalar decompletion is now ruled out as the missing weld.

## Log (cont. 18)

- 2026-07-10 — wave 16: attacked the apparent `(s-1)` repair, isolated its loss of `L1`, raised the
  smoothing order minimally, formalized the exact four-knot completed charge, and proved the
  uniqueness/loss-of-Gamma obstruction. Targeted module checks only; no umbrella build.

## Wave 17 — the actual completed source is a two-sided theta seam

71. **Target source exposed.** `[PROVED Lean]` The existing mathlib construction gives
    `completedRiemannZeta_0(s)=mellin(F,s/2)/2` for the modified even theta kernel `F`. The critical
    logarithmic normalization is `h(u)=exp(u/4)F(exp u)`.
72. **Constraint fixed point.** `[PROVED HERE + Lean]` The theta reciprocal law becomes the exact
    reflection constraint `h(-u)=h(u)`. The positive theta series proves `h(u)!=0` for every
    `u!=0`.
73. **Canonical half-source split.** `[PROVED HERE + Lean]` With
    `h_+=1_(0,infinity)h`, the full source satisfies `h(u)=h_+(u)+h_+(-u)` pointwise. The positive
    half directly discharges `HasAELowerSupport h_+ 0`; the reflected half is exactly the
    negative-half truncation.
74. **Full-source support obstruction.** `[PROVED HERE + Lean]` The actual completed source has no
    finite lower-support threshold. Thus it cannot be passed wholesale to the Sonin support
    transfer. The reflected half is nonzero and forced by completion, not optional defect data.
    Complete proof: `../2-fully-proven/new/xi-theta-source-seam.md`.
75. **Next open coordinate.** `[OPEN CORE]` Build a bounded non-diagonal coefficient reader on
    `h_+` and compute the exact negative-line charge of `h_+(-u)`. The Blaschke candidate exists but
    has archimedean condition number growing like `sinh(pi n)`.

## Log (cont. 19)

- 2026-07-10 — wave 17: formalized the actual completed theta source, proved evenness and two-sided
  nonvanishing, split it into a lower-supported half plus exact reflection, discharged the half
  support Prop, and ruled out lower support for the full target. Targeted module build only; no
  umbrella build.

## Wave 18 — finite theta readers expose exponential conditioning

76. **Exact finite reader.** `[SEARCH + Lean infrastructure]` The normalized right-half-plane
    Blaschke probe `Q_(n,N)` equals `1` at `n^2` and annihilates every other square `m^2` with
    `1<=m<=N`.
77. **Boundary localization.** `[PROVED Lean]` Each Blaschke factor has unit modulus on the imaginary
    boundary, so every amplification cost lies in the interpolation normalizers.
78. **Exponential lower bound.** `[PROVED HERE + Lean]` The `floor(n/2)` lower-band factors each
    contribute at least `5/3`; consequently
    `||Q_(n,N)(0)|| >= 2(5/3)^floor(n/2)` for `N>=n>=2`.
79. **Novelty gate retained.** `[BRIDGE]` The finite interpolation algebra is formal infrastructure,
    not a new-knowledge claim. The live theorem remains the optimal infinite norm
    `sqrt(2/pi)sinh(pi n)` and, critically, the transform that makes its Hardy pairing a coordinate
    of the completed Mellin source.

## Log (cont. 20)

- 2026-07-10 — wave 18: formalized finite theta-square Blaschke readers, exact interpolation,
  imaginary-boundary unit factors, and exponential conditioning. Targeted module build only; no
  umbrella build.

## Wave 19 — the completed trace selects log translations, and truncation creates a moving boundary

80. **Transform bridge adjudicated.** `[PROVED HERE + Lean]` On the critical line,
    `completedRiemannZeta_0(1/2+it)=Fourier(h)(t/(4*pi))/2`. Mellin convergence of the strong theta
    FE-pair directly discharges integrability of `h`, `h_+`, and its reflection; no analytic Prop is
    introduced.
81. **Positive cosine trace.** `[PROVED HERE + Lean]` Reflection gives
    `Fourier(h)(w)=Fourier(h_+)(w)+Fourier(h_+)(-w)`. Since `h_+` is real,
    `completedRiemannZeta_0(1/2+it)=Re(Fourier(h_+)(t/(4*pi)))` exactly. The apparent real-part loss
    is not claimed non-injective: half-line cosine transforms may retain the source.
82. **Blaschke consumer retired.** `[FALSIFIED]` The square-rate Blaschke probe reads a Laplace
    variable in `exp(-pi*m^2*x)`, while the completed trace is Fourier after `x=exp(u)`. The actual
    atoms are `2*exp(u/4-pi*m^2*exp(u))`, not exponentials in `u`. The finite probe remains correct
    infrastructure but does not act on the completed trace.
83. **Log-translation coordinate.** `[PROVED HERE + Lean]` Every square atom is
    `m^(-1/2)*psi(u+2*log(m))` for the common mother `psi(u)=2*exp(u/4-pi*exp(u))`. Thus Fourier in
    `u` diagonalizes the relevant full-line translations.
84. **Moving-boundary seam.** `[PROVED HERE + Lean]` Positive truncation fails to commute with a
    forward translation by `a`: the exact commutator is the translated profile restricted to
    `(-a,0]`. Its Fourier coordinate is exactly a translation phase times the Fourier transform of
    the mother profile restricted to `(0,a]`. For the `m`-th square atom this produces an explicit
    finite-window boundary charge on an interval of length `2*log(m)`. Complete proof:
    `../2-fully-proven/new/xi-theta-critical-log-translation-seam.md`.
85. **New open core.** `[OPEN CORE]` Decide whether the nested finite-window transforms
    `Fourier(1_(0,2log(m)]*psi)` admit a stable triangular coefficient reader and then compose that
    reader with the balanced Perron seam. The obstruction is now a concrete index-dependent boundary
    charge, not reciprocal-Gamma scalar decompletion and not a hypothetical Hardy pairing.

## Log (cont. 21)

- 2026-07-10 — wave 19: proved the exact critical Fourier and positive cosine trace, discharged the
  source integrability interfaces, falsified the Laplace/Blaschke consumer by variable comparison,
  and formalized square atoms as log-translates with their exact truncation commutator and
  finite-window Fourier boundary coordinate. Targeted module checks only; no umbrella build.

## Wave 20 — the correct theta reader is superexponentially conditioned

86. **Physical atom mass.** `[PROVED HERE + Lean]` The strict positive-half square atom
    `a_m(u)=1_(0,infinity)(u)*2*exp(u/4-pi*m^2*exp(u))` satisfies
    `a_m(u)<=2*exp(-pi*m^2)*exp(-2u)`. Hence its logarithmic `L1` mass is at most
    `exp(-pi*m^2)`.
87. **Completed critical samples stay small.** `[PROVED HERE + Lean]` Every Fourier sample obeys
    `|Fourier(a_m)(w)|<=exp(-pi*m^2)` uniformly in the critical frequency. Completion does not
    recover the physical scale at finitely many sample points.
88. **Finite-sampler obstruction.** `[PROVED HERE + Lean]` Any finite weighted sampler normalized by
    `sum_j c_j*Fourier(a_m)(w_j)=1` has total weight
    `sum_j |c_j|>=exp(pi*m^2)`.
89. **Continuous-reader obstruction.** `[PROVED HERE + Lean]` Any continuous linear functional on
    logarithmic `L1` satisfying `R_m(a_m)=1` has operator norm at least `exp(pi*m^2)`. Thus the
    correct transform is more severely conditioned than the retired Blaschke reader's
    `exp(pi*m)` scale. Complete proof:
    `../2-fully-proven/new/xi-theta-reader-superexponential-conditioning.md`.
90. **Stable triangular candidate refuted.** `[FALSIFIED]` The nested windows admit uniformly bounded
    finite-sample or `L1`-continuous coefficient readers. Exact recovery remains possible only via
    an unbounded boundary asymptotic or a stronger analytic topology.
91. **New open core.** `[OPEN CORE]` Construct an intrinsic completed-carrier norm that offsets the
    physical `exp(-pi*m^2)` decay and simultaneously controls the balanced Perron charge, without
    inserting reciprocal-Gamma or `exp(pi*m^2)` decompletion by definition.

## Log (cont. 22)

- 2026-07-10 — wave 20: attacked the stable nested-window reader, proved superexponential decay of
  each correct positive theta atom in both physical `L1` and every critical Fourier sample, and
  derived matching lower bounds for finite-sample and continuous `L1` reader condition numbers.
  Targeted module verification only; no umbrella build.

## Wave 21 — the heat reader survives as a composite fixed-index constraint

92. **Conditioning attack corrected.** `[FALSIFIED]` The lower bound `exp(pi*m^2)` by itself kills
    the Perron route. Perron fixes `m` before contour depth tends to infinity, so any finite
    `m`-dependent constant may be paid. The theorem rules out uniform weak-topology readers, not a
    fixed-index reader.
93. **Exact heat reparametrization.** `[PROVED HERE + Lean]` Removing the critical logarithmic weight
    and applying `y=exp(u)-1` sends the `m`-th physical square atom to
    `exp(-pi*m^2)*exp(-pi*m^2*y)` pointwise for `y>0`.
94. **Condition number explained.** `[PROVED HERE + Lean]` Multiplication by `exp(pi*m^2)` removes
    exactly the `x=1` boundary shift and recovers the ordinary heat atom `exp(-pi*m^2*y)`. The
    superexponential cost is a geometric boundary normalization, not a new reciprocal-Gamma wall.
95. **Blaschke route reopened in composite form.** `[PROVED ATOM BRIDGE]` The direct pairing of the
    critical Fourier trace with a Laplace reader remains false, but the chain inverse log-Fourier ->
    positive source -> heat reparametrization -> boundary denormalization reaches the exact atom
    family consumed by half-plane Hardy readers. Complete proof:
    `../2-fully-proven/new/xi-theta-heat-reparametrization.md`.
96. **Intrinsic heat Hilbert topology.** `[PROVED HERE + Lean]` The nonlinear heat map satisfies
    `integral_(y>0)|T(f)(y)|^2=(1/4)integral_(u>0)exp(u/2)|f(u)|^2`. Thus it is one half of an
    isometry from a coefficient-independent Jacobian-weighted source space to ordinary heat `L2`;
    no change-of-measure Prop remains.
97. **New open core.** `[OPEN CORE]` Build the infinite square-rate Paley-Wiener reader in these
    explicit Hilbert spaces without an existence Prop, and transport its reflected contribution
    through the balanced Perron seam. Retired card: `../5-failed/theta-composite-heat-reader.md`.

## Log (cont. 23)

- 2026-07-10 — wave 21: attacked the interpretation of the conditioning theorem, restored the
  fixed-index route, formalized the exact log-source to shifted-heat atom map, and identified the
  exp(pi*m^2) reader cost with the physical `x=1` boundary shift, and proved the exact
  Jacobian-weighted `L2` identity for the composite heat map. Targeted verification only; no
  umbrella build.

## Wave 22 — the infinite reader is forced singular at the compactified heat boundary

98. **Compactified heat nodes.** `[PROVED HERE + Lean]` The square-rate nodes
    `x_m=exp(-pi*m^2)` are positive and converge to zero.
99. **Holomorphic moment-reader obstruction.** `[PROVED HERE + Lean]` If a symbol is holomorphic on
    a connected compactified domain containing zero and all nodes, and vanishes at every `x_m`
    except possibly `x_n`, then the isolated-zero principle forces it to vanish at `x_n` too.
    Hence no such symbol realizes the infinite Kronecker-delta reader.
100. **Finite Lagrange limit refuted.** `[FALSIFIED]` Finite polynomial readers can converge locally
    uniformly on a connected compactified domain to a holomorphic delta symbol retaining all
    infinite node constraints. Such a limit would contradict the preceding obstruction.
101. **Forced boundary singularity.** `[PROVED NEW]` Every exact infinite reader represented by a
    connected-domain compactified moment symbol must be singular or nonanalytic at `x=0`. Under
    `z=-(1/pi)log(x)`, that boundary is moved to infinity and the nodes become `m^2`; the rate-plane
    Hardy/Blaschke category is therefore structurally selected rather than optional. Complete proof:
    `../2-fully-proven/new/xi-theta-heat-node-singularity.md`.
102. **New open core.** `[OPEN CORE]` Construct the singular rate-plane reader and its source-side `L2`
    representative, then compute the reflected balanced-Perron charge.

## Log (cont. 24)

- 2026-07-10 — wave 22: attacked three reader categories, ruled out the analytic compactified-moment
  category by an isolated-zero theorem, and localized the unavoidable singularity exactly at the
  compactified heat boundary. Targeted verification only; no umbrella build.

## Wave 23 — explicit infinite square-rate reader and exact boundary energy

103. **Canonical rate-plane symbol.** `[PROVED HERE + Lean]` The closed form
     `B(z)=sin(pi*sqrt(z))/sinh(pi*sqrt(z))` vanishes at every positive square. Its derivative at
     `n^2` is nonzero.
104. **Infinite delta interpolation.** `[PROVED HERE + Lean]` Inverse-slope normalization of the
     removable difference quotient at `n^2` gives one at `n^2` and zero at every other square, with
     no finite cutoff and no reader-existence Prop. Rescaling by `s/pi` gives the same result at the
     physical heat rates `pi*m^2`. Complete proof:
     `../2-fully-proven/new/xi-theta-square-rate-reader-symbol.md`.
105. **Boundary inner identity.** `[PROVED HERE + Lean]` On the punctured imaginary boundary the sine
     and hyperbolic-sine terms have equal norm, so `|B(it)|=1`. The normalized reader has the exact
     Cauchy profile forced by the node slope.
106. **Exact condition number.** `[PROVED HERE + Lean]` The dimensionless boundary energy is
     `(4/pi)*sinh(pi*n)^2`; after restoring the physical rate it is `4*sinh(pi*n)^2`. Hence the
     standard normalized boundary norm is exactly `sqrt(2/pi)*sinh(pi*n)`, matching the value that
     was previously only predicted. Complete proof:
     `../2-fully-proven/new/xi-theta-square-rate-boundary-energy.md`.
107. **Interfaces discharged.** `[PROVED]` Infinite symbol existence, finite-cutoff dependence,
     boundary integrability, and boundary-norm hypotheses are eliminated. The compactified symbol
     obstruction and the rate-plane construction now meet exactly: the singular compactified
     boundary is the inner boundary at rate infinity.
108. **New open core.** `[OPEN CORE]` Prove analytic right-half-plane membership and uniform interior
     Hardy control, construct the Paley-Wiener `L2` representative, and compute its reflected
     balanced-Perron charge.

## Log (cont. 25)

- 2026-07-10 — wave 23: constructed the exact infinite square-rate reader symbol, proved its simple
  node normalization at every physical theta heat rate, proved the punctured-boundary inner identity,
  and derived the exact normalized boundary condition number. Targeted verification only; no
  umbrella build.

## Wave 24 — the H2 and Paley-Wiener reader is canonical on paper

109. **Selected-zero factorization.** `[PROVED PAPER]` Factoring the physical inner product as
     `B_phys=b_n*B_n` rewrites the reader as
     `R_n(s)=-B_n(s)/(B_phys'(lambda_n)(s+lambda_n))`, where `B_n` is inner.
110. **Uniform interior control.** `[PROVED PAPER]` The factorization gives a Cauchy majorant on every
     right-half-plane line and bounds the full Hardy supremum by the proved boundary energy.
     Dominated convergence at the boundary gives equality.
111. **Exact Hardy norm.** `[PROVED PAPER]` In the standard `1/(2pi)` normalization,
     `||R_n||_H2=sqrt(2/pi)*sinh(pi*n)`.
112. **Canonical source reader.** `[PROVED PAPER]` Define `r_n=PW^(-1)(R_n)` under the unitary Laplace
     Paley-Wiener map. Then `r_n` has the same exact norm and pairs to the Kronecker delta against
     every heat exponential `exp(-pi*m^2*y)`. Fixed multiplication by `exp(pi*n^2)` reads the
     boundary-shifted theta atoms. Complete proof:
     `../2-fully-proven/new/xi-theta-square-rate-hardy-reader.md`.
113. **New open core.** `[OPEN CORE]` Express the resulting fixed-index reader directly on the
     completed critical cosine trace and compute its reflected contribution through the balanced
     third-order Perron seam. The Lean-only gap is the missing half-plane H2/Paley-Wiener unitary API.

## Log (cont. 26)

- 2026-07-10 — wave 24: factored the selected Blaschke zero, proved uniform interior Hardy control
  and the exact H2 norm on paper, and defined the canonical source-side L2 reader by inverse
  Paley-Wiener. No umbrella build.

## Wave 25 — the positive theta half is the unit-radius Perron source

114. **Reflected-charge premise corrected.** `[FALSIFIED]` The reflected theta half contributes an
     independent lower-supported Perron charge after the critical cosine reduction. It is
     upper-supported, while its Fourier transform is already the conjugate of the real positive
     half's transform. Reflection is fixed cosine data, not a second source variable.
115. **Intrinsic theta envelope.** `[PROVED HERE + Lean]` With
     `C_theta=evenKernel(0,1)-1`, the actual positive half satisfies
     `|h_+(u)|<=C_theta*exp(-2u)` for all `u`, and hence `|h_+(u)|<=C_theta`.
116. **Actual-source L2 interface.** `[PROVED HERE + Lean]` Mellin convergence gives `h_+ in L1`;
     the intrinsic bound gives `|h_+|^2<=C_theta|h_+|`, hence `h_+ in L2`. Its canonical `SoninL2`
     class agrees with the explicit source almost everywhere and discharges lower support at
     threshold zero without a source-existence Prop.
117. **Unit Perron radius.** `[PROVED HERE + Lean]` The negative-line source charge satisfies
     `|Src_(M,n,delta)(h_+)|<=kappa||h_+||_2(n-delta)^(1-M)` and tends to zero whenever
     `n-delta>1`.
118. **Canonical theta seam.** `[PROVED HERE + Lean]` Carrier flank `L2` energy now constructs the
     additive defect relative to `h_+` internally. Under the existing horizontal mass and raw
     Dirichlet-edge hypotheses, its normalized Perron coordinate converges to the coefficient.
     Both the abstract source witness and defect-existence Prop are removed. Complete proof:
     `../2-fully-proven/new/xi-theta-unit-radius-perron-source.md`.
119. **New open core.** `[OPEN CORE]` The source side is complete. Construct a non-diagonal completed
     coefficient extractor retaining Gamma-driven vertical decay while exposing a fixed raw
     arithmetic coefficient. Scalar decompletion cannot supply both properties; the Hardy heat
     reader is valid infrastructure but does not itself repair this carrier mismatch.

## Log (cont. 27)

- 2026-07-10 — wave 25: attacked the reflected-charge premise, proved the actual positive theta
  source is a canonical lower-supported `L2` object of Perron radius one, and combined it with the
  canonical seam to remove both source-existence and defect-existence interfaces. Targeted module
  verification only; no umbrella build.

## Wave 26 — the theta moving boundary is a flat flow coboundary

120. **Carrier ontology rejected.** `[FALSIFIED]` Building an `M`-indexed carrier around the theta
     source advances the native constraint. The construction transports vertical-line data and is
     therefore a flow in disguise.
121. **Projection commutator.** `[PROVED HERE + Lean]` For forward logarithmic translation `T_a` and
     strict positive projection `P_+`, the swept boundary is exactly
     `B_a=T_a P_+-P_+ T_a` for every `a>0`.
122. **Exact conjugation coboundary.** `[PROVED HERE + Lean]` After inverse-translation normalization,
     `D_a=B_a T_(-a)=T_a P_+ T_(-a)-P_+`. Thus the entire moving-window family has the explicit
     primitive `P_+`.
123. **Flat cocycle law.** `[PROVED HERE + Lean]` The windows satisfy
     `B_(a+b)=B_a T_b+T_a B_b`; the normalized defects satisfy
     `D_(a+b)=T_a D_b T_(-a)+D_a`. Their translation curvature vanishes identically.
124. **Theta specialization and route closure.** `[PROVED HERE + Lean]` At every square index `m>1`,
     with `a_m=2log m`, the theta moving boundary is `D_(a_m)(T_(a_m)thetaLogMother)`. Hence every
     index-dependent boundary charge is an evaluation of one exact flow coboundary and vanishes in
     any obstruction quotient modulo affine gauge. Complete proof:
     `../2-fully-proven/new/xi-theta-boundary-coboundary-no-go.md`.
125. **New open core.** `[OPEN CORE]` Work only with the fixed completed datum. Map the
     completed-theta/prime weld to a nonzero carrier-free obstruction class surviving all affine
     translation/scaling coboundaries, and connect that class to FE polarization. No evolving
     carrier, contour-depth family, or projection commutator qualifies.

## Log (cont. 28)

- 2026-07-10 — wave 26: accepted the carrier-is-flow objection, tested the moving boundary for
  cohomological content, proved it is an exact flat conjugation coboundary, and retired the composite
  theta reader/carrier as an RH route. Targeted module verification only; no umbrella build.

## Log (cont. 12)
- 2026-07-10 — Q-COC (§36) LANDED: `QuietCrossingCocycle.lean` (hand-written port of the
  conductor module with the datum abstracted; 2 fix cycles). `quiet_crossing_cocycle_bound`:
  ‖aₙ‖ ≤ 4·H(M)·B·(n−½)^{1−M} at every depth M ≥ max(2,c) with flank bound ‖h‖ ≤ H(M) on
  −M ≤ Re s ≤ 1−c; `quiet_crossing_cocycle_support`: H(M) ≤ C·r^M (r ≥ 1) ⟹ aₙ = 0 for
  n − ½ > r — support radius = exponential flank rate, machine-checked. During formalization
  the C ≥ 0 hypothesis proved redundant and was dropped. Verified: standalone compile clean
  (zero warnings), both theorems axiom-clean [propext, Classical.choice, Quot.sound], formal
  lint passed, index regenerated, umbrella import added. Note: the full umbrella build currently
  fails in `XiThetaBoundaryCoboundary.lean` — a module added concurrently by another agent
  (07:21 today), unrelated to this lane; Q-COC's own target builds green.

## Wave 11 — the kill theorem: minimal non-conductor divisors are quiet-unrealizable

38. **Consistency instantiation `[PROVED-by-instantiation]`.** `quiet_crossing_cocycle_support`
    with `h ≡ 1`, `H ≡ 1`, `C = r = 1` re-derives the banked `quiet_crossing_rigidity`
    conclusion (`aₙ = 0` for all `n ≥ 2`); the new module strictly subsumes both the symmetric
    and the conductor theorems.
39. **`quiet_crossing_cocycle_kill` `[PROVED — Lean, axiom-clean]`.** Bounded flank data
    (`H(M) ≤ C` uniformly — any finite Blaschke-type quotient with poles off the closed flank
    region) gives support radius 1, so the carrier collapses to the constant `a₁`; the identity
    principle spreads the constant to all of ℂ; and evaluating the functional equation **at a
    zero `ρ₀` of the reflection factor** kills the constant: `a₁ = h(ρ₀)·F(1−ρ₀) = 0`. The
    divisor itself executes the kill — no genericity hypothesis needed. Conclusion: `aₙ = 0` for
    ALL `n ≥ 1`. The minimal non-conductor divisor (one zero/pole pair `ρ₀ ↔ 1−ρ₀`, e.g.
    `h = (s−ρ₀)/(s−(1−ρ₀))`, which satisfies the exact cocycle law) carries no nonzero quiet
    Dirichlet series: **realizable divisors are either empty or force unbounded flank growth.**
40. **Paper extension (a.p.-divisor argument, [SEARCH]-adjacent tools).** With a conductor
    factor, `H(M) ≤ C·e^{aM}` still gives finite support ⟹ Dirichlet polynomial ⟹ the cocycle is
    a ratio of Dirichlet polynomials, whose zero/pole sets are Bohr almost-periodic with positive
    density per height (Jessen–Tornehave); an a.p. difference divisor is empty or infinite, never
    finite-nonempty ⟹ conductor × finite nontrivial Blaschke is also unrealizable. Combined with
    39 and the Q-COC dichotomy (§37): **the realizable divisor ladder starts at empty (conductor
    class) and jumps directly to infinite divisors at Γ-scale flank growth — the first two rungs
    of the Selberg shape axiom are now derived, conditional only on one quiet height sequence.**

## Log (cont. 13)
- 2026-07-10 — wave 11: `quiet_crossing_cocycle_kill` appended to QuietCrossingCocycle.lean
  (3 fix cycles: analyticOnNhd spelling via Complex.analyticOnNhd_univ_iff_differentiable,
  domain annotation on the constant). Verified: standalone clean zero warnings, module build
  8477 jobs green, all THREE public theorems [propext, Classical.choice, Quot.sound], lint
  passed, index regenerated. h≡1 instantiation checked (subsumes quiet_crossing_rigidity).

## Wave 27 — the weld is absolute-exact but FE-relatively nontrivial

126. **Coefficient-category audit.** `[PROVED HERE + Lean]` The scalar weld cocycle
     `omega_theta(g,h)=theta*m_g*n_h` is nonzero for `theta!=0` with trivial real coefficients, but
     its equivariant lift to the minimal affine module `<D,I>` is exact.
127. **Explicit affine primitive.** `[PROVED HERE + Lean]` Under the conjugation action
     `g.(aD+bI)=aD+(b-a*n_g*theta)I`, the cochain
     `b_theta(m,n)=mD-theta*m*n*I` satisfies `delta b_theta=omega_theta I`. This module is forced by
     the fixed operator identity `M_p^(-1) D M_p=D-log(p)I`, not chosen to kill the class.
128. **Primitive rigidity.** `[PROVED HERE + Lean]` Every affine primitive of a nonzero weld cocycle
     has `D`-coefficient exactly one at the derivation generator. Evaluating the two ordered generator
     pairs and subtracting forces `theta*a=theta`.
129. **FE-relative survival.** `[PROVED HERE + Lean]` Functional-equation reflection fixes `I` and
     reverses `D`; Lean also proves `xi'(1-s)=-xi'(s)`. Hence no FE-fixed affine cochain can
     trivialize the weld. At each prime rate `theta=log p`, the affine class is absolutely zero but
     FE-relatively nontrivial. Complete proof:
     `../2-fully-proven/new/weld-affine-coefficient-collapse.md`.
130. **New open core.** `[OPEN CORE]` Replace the external `ClassInducesJ` Prop by an FE-relative
     second constraint cohomology quotient whose allowed primitives are FE-fixed, and construct a
     canonical map from the prime relative class to the fixed FE Krein polarization. No carrier or
     evolution parameter is admissible.

## Log (cont. 29)

- 2026-07-10 — wave 27: compared the abstract scalar weld with the natural operator coefficient
  category, proved absolute affine collapse, proved every primitive must contain the
  reflection-odd derivation, and isolated the surviving weld as an FE-relative obstruction.
  Targeted module verification only; no umbrella build.

## Wave 28 — FE covariance kills the relative route; differential order is the surviving constraint

131. **Wave-27 FE claim corrected.** `[FALSIFIED]` Entry 129 treated FE reflection as acting
     pointwise on coefficient values while leaving the weld-group label fixed. The genuine
     functional equation also inverts both labels: `tau(m,n)=(-m,-n)`, since `D` reverses and
     `R M_p R=p^(-1) M_p^(-1)` modulo the central scalar. The pointwise-fixed quotient was not an
     FE-relative cohomology and is retired.
132. **FE-covariant affine collapse.** `[PROVED HERE + Lean]` With
     `R(aD+bI)=-aD+bI`, the explicit primitive satisfies
     `R b_theta(m,n)=b_theta(-m,-n)`. Hence the natural affine trivialization is genuinely
     FE-covariant. Completion symmetry alone does not restore the weld class.
133. **Exact order filtration.** `[PROVED HERE + Lean]` Principal symbol gives an equivariant exact
     coefficient sequence `0 -> R I -> R D direct-sum R I -> R sigma(D) -> 0`. The derivation-count
     one-cocycle `ell(m,n)=m` lifts to `b_theta`, and `delta b_theta=omega_theta I`; the weld is the
     connecting boundary of this fixed filtration.
134. **Order-zero survival.** `[PROVED HERE + Lean]` Every affine primitive has principal symbol one
     at the derivation generator. Therefore no pointwise order-zero gauge cochain can trivialize a
     nonzero weld. The resulting order-zero gauge quotient carries a nonzero class at every prime
     rate `theta=log p`, although the unrestricted and FE-covariant affine classes are zero. Complete
     corrected proof: `../2-fully-proven/new/weld-affine-coefficient-collapse.md`.
135. **New open core.** `[OPEN CORE]` In the fixed completed representation, prove that every bounded
     polarization-preserving gauge has differential order zero and construct the canonical map from
     the prime filtration boundary to the existing Krein form. This is the concrete replacement for
     `ClassInducesJ`; no carrier or evolution parameter is admissible.

## Log (cont. 30)

- 2026-07-10 — wave 28: attacked the proposed FE-relative quotient with the full semilinear FE
  action, falsified it, formalized the FE-covariant primitive, and relocated the surviving weld to
  the connecting boundary of the differential-order filtration. Targeted verification only; no
  umbrella build.

## Wave 12 — walked to conclusion: the consistency audit, the m < 1 slice, and where the machine ends

41. **Mandatory consistency audit — and a scope correction to §37/§40.** Test object: `L(s,χ)`,
    χ real primitive — entire, quiet (strip convexity gives `q_k ~ T^{3/2} = o(T²)`), unit
    coefficients, self-FE. The support/decay reading would kill its coefficients — so a
    hypothesis must fail, and it does: by Stirling the Γ-quotient reflection factor grows like
    `|t|^{(1−2σ)/2}` on `Re s = σ` — polynomially in HEIGHT, with exponent growing linearly in
    the depth `M`. The t-uniform `hgrow` of waves 10–11 correctly excludes every Γ-type factor.
    §37/§40 hold as stated for t-uniform (and now sub-critical t-polynomial) flanks; Γ-data live
    outside that slice by construction, not by accident.
42. **The full convergence slice, formalized `[PROVED — Lean, axiom-clean ×3]`.**
    `QuietCrossingCocycleTPoly.lean`: flank bounds `‖h(s)‖ ≤ H(M)·(2+|Im s|)^m` with FIXED
    `m < 1`. `quiet_crossing_cocycle_bound_tpoly`: `‖aₙ‖ ≤ (12/π)·J(m)·H(M)·B·(n−½)^{1−M}`,
    `J(m) = ∫(1+y²)^{(m−2)/2}dy` (finite ⟺ m < 1, via mathlib's Japanese-bracket lemma at
    exactly `r = 2−m > 1`); `support_tpoly` (radius `r` from `H(M) ≤ C·r^M` — the height aspect
    never enters the support radius); `kill_tpoly` (bounded depth aspect + a zero ⟹ `F ≡ 0`).
43. **Where the machine ends — and why that is the right ending.** The threshold `m < 1` is
    structural: the Perron kernel decays like `|y|^{−2}`, so `|y|^m·|y|^{−2}` is integrable
    exactly for `m < 1`. A reflection factor of Selberg degree `d` has height exponent `≈ d·M`
    at depth `M` — exceeding every fixed `m`; kernel escalation to degree `K` buys `m < K` but
    plants kernel poles at `0, −1, …, −K`, forcing `M > K`, so the escalation ladder closes only
    while (height exponent per unit depth) < 1 — i.e. **for degree < 1**. There the machine
    proves the carrier is a Dirichlet polynomial with conductor cocycle: a quiet-conditional,
    Perron-rectangle derivation of the Kaczorowski–Perelli degree gap `(0,1)` `[BRIDGE — new
    mechanism for a known theorem]`. At degree exactly 1 the machine's convergence fails at the
    same line where ζ and the Dirichlet L-functions exist. **The machine saturates precisely at
    the archimedean existence line: its analytic failure mode IS the Γ-factor.** Γ-extremality
    in mechanical form — the constraint-side derivation the card's Goal asked for, with the
    completed L-functions appearing as the unique boundary inhabitants rather than postulated
    shapes.

## Log (cont. 14)
- 2026-07-10 — wave 12 (walk to conclusion): L(χ) audit run (no contradiction — t-uniformity
  excludes Γ-data correctly; §37/§40 scoped); QuietCrossingCocycleTPoly.lean LANDED (4 fix
  cycles; verified: standalone clean zero warnings, module build 8477 jobs green, all three
  theorems [propext, Classical.choice, Quot.sound], lint passed, index regenerated, umbrella
  import added). Degree-gap reading recorded as [BRIDGE — new mechanism]. Beyond the slice:
  M-dependent kernel escalation = the named major program (degree ladder above 1).

## Wave 29 — bounded spectral gauge forces the order filtration

136. **FE label action grounded.** `[PROVED HERE + Lean]` The fixed Euler multiplier satisfies
     `R M_p R=p^(-1) M_p^(-1)` pointwise, while `R D R=-D`; inversion of both weld labels is now a
     concrete operator theorem rather than a stipulated group involution.
137. **Spectral derivation is unbounded.** `[PROVED HERE + Lean]` On the fixed critical-line space
     `L^2(R)`, the norm-one packets `u_N=1_[N,N+1]` satisfy
     `||X u_N||_2>=N` for coordinate multiplication `X`. No bounded operator agrees with `X` on this
     explicit domain.
138. **Bounded affine rigidity.** `[PROVED HERE + Lean]` If a bounded operator agrees with `aX+bI`
     on every `u_N`, then `a=0`: otherwise `a^(-1)(T-bI)` is a bounded realization of `X`. Thus every
     data-bearing bounded affine weld cochain is automatically order zero; the admissibility
     condition is derived rather than postulated.
139. **Bounded prime obstruction.** `[PROVED HERE + Lean]` Combining bounded affine rigidity with
     primitive-symbol rigidity proves that no bounded spectral affine cochain trivializes a nonzero
     weld cocycle. In particular no bounded primitive exists at `theta=log p` for any prime `p`.
     Complete proof: `../2-fully-proven/new/weld-affine-coefficient-collapse.md`.
140. **New open core.** `[OPEN CORE]` Construct a canonical map from this bounded prime filtration
     obstruction to the fixed FE Krein form and delete the plain-linear `ClassInducesJ` interface.
     The bounded-to-order-zero step is closed; only the class-to-form map remains.

## Log (cont. 31)

- 2026-07-10 — wave 29: grounded the full FE generator action, proved spectral-coordinate
  unboundedness on fixed `L^2(R)`, derived order-zero gauge from bounded realizability, and excluded
  every bounded affine primitive of the prime weld. Direct checks on touched modules only; no
  project-wide lint or build.

## Wave 30 — the weld class determines area, not `J`; positive pullbacks cannot reach the seam

141. **Canonical class output.** `[PROVED HERE + Lean]` The scalar weld-class line is additively
     equivalent to its conversion-rate coordinate and maps injectively to the alternating generator-
     plane form `Omega_theta(x,y)=theta*(x_1*y_2-x_2*y_1)`. This is an explicit homomorphism, not an
     external relation.
142. **`ClassInducesJ` interface no-go.** `[PROVED HERE + Lean]` No complex structure can be natural
     under all automorphisms preserving `Omega_theta`. The area-preserving upper shear fixes `e_1`;
     a commuting `J` would send `e_1` into the shear-fixed real line, giving a forbidden real
     eigendirection for `J^2=-1`. The weld class alone cannot canonically induce `J`.
143. **Correct polarization direction.** `[PROVED HERE + Lean]` An independently fixed complex
     structure and a compatible alternating form canonically give
     `Q(x,y)=Omega(x,Jy)`, symmetric and `J`-preserved, with the mixed form recovering `-Omega`.
     For the standard generator-plane `J`, `Q_theta=theta*I`; every prime rate is positive definite.
144. **Positive-pullback no-go.** `[PROVED HERE + Lean]` Every congruence pullback of the local prime
     Gram remains Krein-nonnegative. By the existing exact-inertia theorem, a nondegenerate factored
     Krein form carrying an off-line pair is not nonnegative and therefore cannot be any such
     pullback. Complete proof: `../2-fully-proven/new/weld-class-determines-area-not-j.md`.
145. **New open core.** `[CONJECTURE / OPEN CORE]` The RH-bearing form must be a non-split completed
     extension: its prime restriction is the canonical weld area, while an intrinsically indefinite
     archimedean cross-term has the existing factored Krein form as Schur complement. Construct this
     fixed form and identity; no carrier, flow, positive pullback, or arbitrary `ClassInducesJ`
     relation is admissible.

## Log (cont. 32)

- 2026-07-10 — wave 30: proved the canonical class-to-area map, killed natural class-to-`J`, reversed
  the polarization direction, and combined local positivity with Krein congruence/exact inertia to
  rule out every positive-pullback realization of an off-line seam. Direct module verification only.

## Wave 31 — FE anti-symplectic reflection turns the weld area into the one-pair Krein block

146. **Fixed FE anti-symplectic structure.** `[PROVED HERE + Lean]` On affine coefficients,
     `R_FE(aD+bI)=-aD+bI` is an involution and reverses the canonical weld area:
     `Omega_theta(R_FE x,R_FE y)=-Omega_theta(x,y)`.
147. **Intrinsic hyperbolic form.** `[PROVED HERE + Lean]` The fixed twist
     `K_theta(x,y)=Omega_theta(x,R_FE y)` is symmetric with Gram
     `[[0,theta],[theta,0]]`. For `theta>0`, `(1,1)` is positive and `(1,-1)` is negative. The
     required indefiniteness comes from FE parity, not from an arbitrary extension or induced `J`.
148. **Exact one-pair identification.** `[PROVED HERE + Lean]` With
     `c=sqrt(theta/2)`, `w=c(1,1)`, and `u=c(1,-1)`, the existing one-pair factored form
     `w*w^*-u*u^*` equals the FE weld Gram exactly for every `theta>=0`; in particular at every prime
     rate `theta=log p`.
149. **Interface discharged locally.** `[PROVED]` The correct local constraint map is now explicit:
     `weld class -> weld area`, followed by `area + fixed FE reflection -> Krein block`.
     `ClassInducesJ`, a positive pullback, and a conjectural Schur-complement extension are all
     unnecessary at the local level. Complete proof:
     `../2-fully-proven/new/weld-class-determines-area-not-j.md`.
150. **New open core.** `[CONJECTURE / OPEN CORE]` Construct the fixed arithmetic incidence map from
     prime-log weld classes and completed FE divisor pairs to the direct sum of these canonical
     hyperbolic blocks, and prove its Gram is the existing global `factoredKreinForm`. The completed
     datum must determine weights and multiplicities; no carrier, flow, or arbitrary pair selection
     is admissible.

## Log (cont. 33)

- 2026-07-10 — wave 31: extracted the anti-symplectic FE involution from the failed positive route,
  constructed its split Krein twist, and identified it exactly with the one-pair factored form at
  every nonnegative and prime rate. Direct module verification only.

## Wave 32 — FE-weld rate blindness kills finite prime-source activation

151. **Positive-rate blindness.** `[PROVED HERE + Lean]` For `theta,eta>0`, the invertible scalar
     change of basis `P=sqrt(theta/eta) I` satisfies `P^* H_eta P=H_theta` for
     `H_theta=[[0,theta],[theta,0]]`. Hence every positive prime FE block has the same Krein
     congruence class; the local hyperbolic shape forgets `log p`.
152. **Exact activation gate.** `[PROVED HERE + Lean]` `H_theta` is Krein-nonnegative iff `theta=0`:
     `(1,-1)` is negative for `theta>0`, while `(1,1)` is negative for `theta<0`. Therefore, for
     every `p>=2`, `H_(a log p)` is nonnegative iff `a=0`.
153. **Finite-source activation obstruction.** `[PROVED HERE + Lean]` A pinned `SigmaSourceMap`
     forces every local count `A(p)` to zero because every finite Euler factor is a unit. Thus every
     associated FE block `H_(A(p) log p)` is the zero matrix, even at a `xi`-zero where
     `analyticOrderAt xi` is nonzero. Complete proof:
     `../2-fully-proven/new/weld-krein-rate-blindness.md`.
154. **Previous open core retired.** `[FALSIFIED]` The one-pair shape identity does not yield a
     finite arithmetic incidence mechanism. Krein congruence cannot distinguish prime rates, and
     pinned prime divisor content activates no block. A `P -> infinity` repair is a cutoff flow;
     setting activation equal to `xi`-multiplicity is tautological.
155. **All factorwise order assemblers excluded.** `[PROVED HERE + Lean]` Package the orders of every
     individual Euler factor together with the archimedean-factor order at a fixed strip point. This
     entire profile is zero. Hence no function of that profile satisfying only `assemble(0)=0` can
     recover the nonzero completed order at a `xi`-zero. The missing datum is genuinely
     non-factorwise; changing the aggregation rule cannot repair the route.
156. **New open core.** `[OPEN CORE]` Locate a fixed completed obstruction class whose restriction to
     every finite Euler/archimedean subalgebra is zero but whose boundary on the completed divisor
     supplies FE-Witt activation. It must be intrinsic, non-carrier, non-limit, and not a renamed
     `analyticOrderAt xi`.

## Log (cont. 34)

- 2026-07-10 — wave 32: proved invertible congruence of all positive FE weld blocks, reduced local
  Krein nonnegativity to the zero/nonzero activation bit, and combined that gate with the finite
  prime-source no-go to prove exact block vanishing at every completed zero. Then excluded every
  zero-preserving assembler from the simultaneous factorwise prime-plus-archimedean order profile.
  Only the new module and its axiom footprint were checked; no project-wide lint or build.

## Wave 33 — the sheared seam is gauge-split; relative cutoff alignment is the real datum

157. **Sheared presentation gauge-trivialized.** `[PROVED HERE + Lean]` With
     `U=[[1,1],[0,1]]`, the alleged non-split presentation satisfies
     `[[X^m,1],[0,1]]=U*diag(X^m,1)`, and `U` has the explicit polynomial inverse
     `[[1,-1],[0,1]]`. The sheared and split matrices present the same torsion module; the shear is
     not an extension class.
158. **Fitting boundary transported exactly.** `[PROVED HERE + Lean]` For every defect `Delta`,
     `Fitting(A_shear,Delta)=Fitting(A_split,U^(-1)Delta)`. The nonzero boundary survives the
     simultaneous gauge, so its source is the pair `(presentation,defect)`, not the presentation
     alone.
159. **Cutoff-crossing is not gauge-natural.** `[PROVED HERE + Lean]` The standard lower crossing is
     a cross-boundary defect before unshearing, but its transport is `[[-1,0],[1,0]]`, which cannot
     equal `(1-e)*sigma*e` for the unchanged `e=diag(1,0)` because its `(0,0)` entry is `-1`.
     Therefore the prior split/sheared contrast held the cutoff coordinates fixed while changing
     target gauge.
160. **Fitting route corrected.** `[FALSIFIED AS STATED]` A more elaborate sheared torsion
     presentation does not supply the non-factorwise completed datum demanded by wave 32. The live
     invariant, if one exists, is the simultaneous-gauge relative position of the divisor lattice,
     a canonical static flag, and the arithmetic action. A carrier-built cutoff supplies that flag
     by a flow and is inadmissible. Complete proof:
     `../2-fully-proven/new/sheared-seam-gauge-trivialization.md`.
161. **New open core.** `[OPEN CORE]` Derive a canonical static flag or filtration from the completed
     Euler-FE object itself and prove that its relative-position class with the local divisor lattice
     controls FE-Witt activation. If no such simultaneous-gauge invariant exists, close the Fitting
     seam route entirely.

## Log (cont. 35)

- 2026-07-10 — wave 33: audited the proposed non-factorwise Fitting survivor under presentation
  equivalence, split the sheared matrix by an explicit unimodular gauge, proved exact Fitting
  transport, and isolated the untransported cutoff alignment as the hidden extra datum. Only the
  new module was compiled and its capstones were axiom-checked.

## Wave 34 — FE parity canonically supplies the flag and makes the shear relatively non-split

162. **Canonical static flag.** `[PROVED HERE + Lean]` FE coefficient reflection is
     `R_FE=diag(-1,1)` on `(D,I)`. Its odd projector `(I-R_FE)/2` is exactly
     `standardCutoff=diag(1,0)`. The flag used by the crossing algebra is therefore fixed by the
     functional equation, not built by a carrier.
163. **Parity-preserving gauge rigidity.** `[PROVED HERE + Lean]` Every polynomial row gauge
     commuting with `R_FE` has zero upper-right entry. Any row factorization
     `A_shear=V*A_split` would force that entry to equal `1`. Hence no FE-parity-preserving row gauge
     can split the sheared presentation, even though an unrestricted unimodular gauge does split it.
164. **First static relative survivor.** `[PROVED AT COEFFICIENT LEVEL]` The sheared seam is trivial
     as an ordinary torsion presentation but nontrivial in the category flagged by FE coefficient
     parity. This is the precise non-carrier relative-position obstruction left after waves 32-33.
165. **Scope attack.** `[OPEN]` The local divisor coordinate is not yet in the theorem. Functional
     equation transports paired germs and acts semilinearly on their coordinates; constant matrix
     commutation alone is not the completed FE-equivariance statement. No RH consequence is claimed.
166. **New open core.** `[OPEN CORE]` Construct the FE semilinear action on paired divisor germs,
     extend the parity flag and sheared presentation to that action, and test whether the resulting
     simultaneous-gauge class maps non-tautologically to FE-Witt activation.

## Log (cont. 36)

- 2026-07-10 — wave 34: derived the standard cutoff as the FE-odd projector and proved that the
  absolutely splitting gauge is forbidden by FE parity, turning the sheared chart into a genuine
  relative obstruction at coefficient level. The same targeted module and axiom audit passed; no
  wider build or lint was run.

## Wave 35 — semilinear FE audit kills the coefficient-level sheared survivor

167. **Paired local-coordinate action.** `[PROVED HERE + Lean]` FE sends the local coordinate at
     `rho` to the negative local coordinate at `1-rho`:
     `((1-s)-(1-rho))=-(s-rho)`. Hence the germ action is semilinear with `X -> -X`; a presentation
     must satisfy `R_t*A(-X)=A(X)*R_s`, not merely constant-matrix commutation.
168. **Forced source parity.** `[PROVED HERE + Lean]` The split order-`m` presentation is
     semilinearly equivariant for target parity `diag(-1,1)` and source parity
     `diag(-(-1)^m,1)`. Both matrices define semilinear involutions. The multiplicity parity enters
     through the unavoidable sign of `(-X)^m`.
169. **Fixed-parity shear failure.** `[PROVED HERE + Lean]` With the same canonical coefficient
     parity frozen on source and target, `[[X^m,1],[0,1]]` is not an FE-semilinear presentation: its
     upper-right equation is `-1=1`. Thus wave 34's coefficient-relative class is not an FE object
     under the fixed action.
170. **Transported-parity collapse.** `[PROVED HERE + Lean]` Transport target parity by the splitting
     gauge `U`, giving `R_t^shear=U*R_FE*U^(-1)`. This is a semilinear involution, the sheared
     presentation becomes equivariant, and `U` is exactly an FE-semilinear isomorphism from the
     split presentation. Simultaneous transport trivializes the class.
171. **Wave-34 survivor corrected.** `[FALSIFIED AS COMPLETED OBSTRUCTION]` The current sheared matrix
     has only two readings: fixed FE actions make it non-equivariant; transported FE action makes it
     split. It supplies no simultaneous-gauge-invariant completed extension. The coefficient-level
     no-splitting theorem remains correct but is not the needed invariant.
172. **New open core.** `[OPEN CORE]` Construct a genuinely non-split FE-semilinear divisor
     presentation with independently fixed source/target involutions and prove non-equivalence under
     every simultaneous equivariant gauge. Only then seek a non-tautological map from its extension
     class to FE-Witt activation.

## Log (cont. 37)

- 2026-07-10 — wave 35: attacked the best coefficient-relative conjecture with the full local FE
  action, formalized `X -> -X`, proved fixed-parity non-equivariance and transported-parity
  split-equivalence, and retired the present sheared Fitting seam as a completed obstruction. Direct
  compilation and axiom checks remained confined to the same touched module.

## Wave 36 — every FE-compatible upper-unit shear is equivariantly split

173. **Polynomial shear classification.** `[PROVED HERE + Lean]` For
     `A_f=[[X^m,f(X)],[0,1]]`, full FE semilinearity is equivalent to `f(-X)=-f(X)`. Thus the
     constant shear was not an isolated failure; all allowed shears are exactly the odd ones.
174. **Splitting parity coincidence.** `[PROVED HERE + Lean]` The elementary splitting gauge
     `U_f=[[1,f],[0,1]]` is FE-semilinear under the identical condition `f(-X)=-f(X)`, and
     `A_f=U_f*diag(X^m,1)`.
175. **Upper-unit family exhausted.** `[PROVED NO-GO]` Every FE-compatible member of the entire
     upper-unit-shear family is FE-semilinearly row-equivalent to the split presentation. Replacing
     `1` by a more elaborate polynomial cannot rescue the route. Complete proof:
     `../2-fully-proven/new/fe-semilinear-upper-shear-exhaustion.md`.
176. **Forced structural move.** `[OPEN CORE SHARPENED]` A genuine extension needs positive torsion
     on both lanes; a unit second lane has no extension content left after FE gauge.

## Log (cont. 38)

- 2026-07-10 — wave 36: classified the full upper-unit shear family and proved FE equivariance is
  exactly the condition making the explicit splitting gauge FE-equivariant. One new module was
  compiled directly and axiom-checked; no broad lint or build.

## Wave 37 — two torsion lanes produce a genuine FE extension and its local Witt activation

177. **Two-torsion FE equation.** `[PROVED HERE + Lean]` For
     `A_(a,b,f)=[[X^a,f],[0,X^b]]`, target parity `diag(-1,1)` forces source parity
     `diag(-(-1)^a,(-1)^b)` and the exact off-diagonal equation
     `-f(-X)=(-1)^b*f(X)`. In particular an order-one second lane permits precisely even `f`.
178. **Constant-term extension classification.** `[PROVED HERE + Lean]` For `b=1`, row splitting is
     equivalent to `X|f`, equivalently `f(0)=0`. Hence an FE-semilinear row-nonsplit extension is
     exactly an even polynomial with nonzero constant term.
179. **Canonical genuine extension.** `[PROVED HERE + Lean]`
     `E_m=[[X^m,1],[0,X]]` is FE-semilinear and has determinant `X^(m+1)`. For `m>0`, it is not
     `U*diag(X^m,X)*V` for any polynomial matrices `U,V`: the split side vanishes entrywise at
     `X=0`, while `E_m` has unit upper-right residue.
180. **Extension-to-Witt activation.** `[PROVED HERE + Lean]` Send the exact extension residue
     `f(0)` to the canonical FE Gram `[[0,f(0)],[f(0),0]]`. The presentation row-splits iff this Gram
     is Krein-nonnegative, and is row-nonsplit iff the Gram has a negative direction. The activation
     scalar is now derived from a gauge obstruction, not inserted by a prime-source map. Complete
     proof: `../2-fully-proven/new/fe-semilinear-two-torsion-extension.md`.
181. **Scope attack.** `[OPEN]` The extension is local and does not yet distinguish zero location.
     It must be attached functorially to the actual completed divisor pair, and its joint
     FE-plus-Schwarz descent must separate the critical-line fixed locus from off-line orbits.
182. **New open core.** `[OPEN CORE]` Compute the Schwarz descent of the constant FE extension class
     on paired divisor germs. If it survives equally on and off the critical line, the new object is
     position-blind; if the fixed-locus descent forces splitting only on the line, it becomes the
     first genuine RH-bearing constraint in this route.

## Log (cont. 39)

- 2026-07-10 — wave 37: replaced the exhausted torsion-plus-unit shear by a two-torsion
  FE-semilinear extension, classified its constant residue, proved genuine two-sided nonsplitting,
  and derived the exact local extension-to-Witt activation equivalence. Verification remained
  limited to the touched modules and their axiom footprints.

## Wave 38 — joint-reflection descent preserves the genuine extension: local Ext is position-blind

183. **Residue reflection invariance.** `[PROVED HERE + Lean]` Local-coordinate reflection
     `X -> -X` preserves the constant extension residue: `(f(-X))(0)=f(0)`. Consequently row
     splitting of `[[X^a,f],[0,X]]` is invariant under reflection.
184. **Witt reflection invariance.** `[PROVED HERE + Lean]` The extension-induced FE Gram depends
     only on `f(0)`, hence `H_(f(-X))=H_f`. Local Krein activation is constant on reflection orbits.
185. **Fixed-germ survival.** `[PROVED HERE + Lean]` For every `m>0`, the unit extension is both
     FE-semilinear and genuinely two-sided nonsplit. Over the rational local ring Schwarz fixes
     coefficients, so at a critical-line fixed germ the joint FE-Schwarz action is the same
     `X -> -X` semilinearity. Fixed-locus descent does not force the class to vanish.
186. **RH-bearing hope retired.** `[FALSIFIED]` A genuine local two-torsion extension and its Witt
     negativity do not distinguish a critical-line fixed germ from a free reflection orbit. The
     local object is new and nontrivial but position-blind. Complete proof and scope correction:
     `../2-fully-proven/new/fe-semilinear-two-torsion-extension.md`.
187. **New open core.** `[OPEN CORE]` Construct a nonlocal orbit-gluing class attached to the fixed
     completed FE-plus-Schwarz groupoid. It must distinguish fixed and free base-point orbits while
     remaining invisible to factorwise order profiles and local extension residues, and it cannot
     be assembled by a carrier or cutoff flow.

## Log (cont. 40)

- 2026-07-10 — wave 38: attacked the genuine two-torsion survivor under joint reflection, proved
  invariance of its residue, splitting class, and Witt block, and showed the equivariant unit class
  survives nonsplit. This rules out local Ext/Witt data as the missing location detector. Only the
  two-torsion module was recompiled and axiom-audited.

## Wave 39 — the integral extension lattice yields a fixed/free Tate orbit detector

188. **Rational blindness explained.** `[BRIDGE]` Over `Q`, averaging by `1/2` kills finite
     stabilizer descent; the reflection blindness of local Ext/Witt is forced by divisibility of the
     coefficient line, not an accidental defect of the chosen matrix.
189. **Canonical integral lift.** `[PROVED HERE + Lean]` The matrix
     `E_m^Z=[[X^m,1],[0,X]]` over `Z[X]` base-changes exactly to the rational FE-semilinear unit
     extension, and its extension residue is the integral unit `1`.
190. **Fixed-orbit survival.** `[PROVED HERE + Lean]` On the fixed residue lattice `Z`, the
     stabilizer norm is `n -> 2n`; reduction modulo two vanishes exactly on norms. The unit residue
     has nonzero fixed-orbit Tate charge.
191. **Free-orbit annihilation.** `[PROVED HERE + Lean]` On the free swap module `Z^2`, every
     invariant pair is diagonal and every diagonal `(c,c)` is the norm of `(c,0)`. In particular the
     unit pair `(1,1)` is invariant but Tate-trivial.
192. **First fixed/free separator.** `[PROVED HERE + Lean]` The same integral two-torsion extension
     gives nonzero descent charge on a fixed germ and zero descent class on a free two-point orbit.
     The separator uses stabilizer gluing, not local position, factorwise orders, or a carrier.
     Complete proof: `../2-fully-proven/new/integral-fixed-free-tate-extension.md`.
193. **New open core.** `[OPEN CORE]` Construct the functorial attachment from the completed ξ
     divisor groupoid to the integral unit extension and prove every actual zero orbit receives the
     odd residue class. Then nonzero descended charge forces nontrivial stabilizer and therefore the
     critical-line fixed locus.

## Log (cont. 41)

- 2026-07-10 — wave 39: retained the integral lattice discarded by the rational local model,
  formalized fixed and free orbit norms, proved the unit residue survives only on fixed orbits, and
  isolated the remaining RH-facing statement as a completed-divisor attachment theorem. One new
  module was compiled directly and its capstones were axiom-checked in scratch.

## Wave 40 — integral Tate detector reduces to existing orbit parity and is retired

194. **Novelty attack.** `[DUAL-GATE FAIL]` The fixed residue `1 mod 2` versus free norm pair
     `(1,1)` is exactly the parity of a one-point versus two-point involution orbit. The existing
     `BandEdgePairing` theorem already states that nonzero unit mod-two flux forces a fixed point.
195. **Attachment circularity.** `[FALSIFIED AS RH INTERFACE]` Assigning the unit residue to each
     orbit makes the charge nonzero precisely when the orbit is fixed. Requiring nonzero charge at
     every ξ-zero orbit therefore restates that every orbit is fixed, i.e. the target location
     conclusion. No arithmetic content was derived.
196. **Status correction.** `[PROVED BRIDGE, NOT NEW KNOWLEDGE]` The integral base-change and norm
     theorems remain valid Lean infrastructure, but the research card is moved to
     `../5-failed/integral-fixed-free-tate-extension.md` and must not be cited as an RH-bearing
     result.
197. **New open core.** `[OPEN CORE]` Find compatibility data in the completed FE/Schwarz gluing that
     is invisible to orbit cardinality, local extension residue, and the exponent-two joint symmetry.
     It must compare the two involution identifications themselves rather than test whether their
     composite fixes the point.

## Log (cont. 42)

- 2026-07-10 — wave 40: attacked the integral Tate proposal against prior Lean work and the novelty
  gate, identified it with the existing fixed-point-free pairing parity theorem, and retired the RH
  interface as circular. The correct algebra remains formalized; the scientific claim is downgraded.

## Wave 41 — the two ordered scalar identifications are gauge-trivial

198. **Correct local object.** `[PROVED HERE + Lean]` At a critical-line two-point orbit, FE and
     Schwarz are two arrows between the same complex germ lines. Their relative composite is an
     anti-linear involution `z -> a*conj(z)` with `a*conj(a)=1`.
199. **Fixed-orbit Hilbert-90 collapse.** `[PROVED HERE + Lean]` Every such coefficient is killed by
     an explicit complex basis gauge (`b=1+a` unless `a=-1`, when `b=i`). A compatible basis at the
     partner germ simultaneously normalizes both FE and Schwarz coefficients to one. In particular
     the leading-jet phase `(-1)^m` is not an invariant without an independently supplied real
     orientation.
200. **Free-orbit flat-square collapse.** `[PROVED HERE + Lean]` On a free four-point orbit, choose
     vertex bases along three edges of the FE/Schwarz square. Exact commutation normalizes the fourth
     edge; the would-be projective multiplier is identically one. A nontrivial multiplier would be
     inserted projective data, not a residue of the completed scalar equations.
201. **Detector exhaustion.** `[PROVED HERE + Lean]` Every scalar detector invariant under the
     natural germ-basis gauges is constant on fixed-orbit data and constant on free-orbit data.
     Hence it factors through a Boolean carrying only fixed/free orbit shape. Comparing the two
     scalar identifications yields no refinement of orbit cardinality. Complete proof:
     `../2-fully-proven/new/fe-schwarz-germ-gluing-gauge-trivialization.md`.
202. **Dual-gate verdict.** `[PROVED NATIVE NO-GO]` Rank-one Hilbert 90 is standard infrastructure;
     the new branch-level result is the exhaustive application to both FE/Schwarz orbit shapes and
     to every gauge-invariant scalar detector. It closes the precise ordered-gluing interface left
     by wave 40.
203. **New open core.** `[OPEN CORE]` Derive from the completed arithmetic datum a nontrivial
     reduction of the complex germ-basis gauge group—a prime grading together with a lattice,
     filtration, or pairing—which is not merely the integral orbit-parity residue. Higher rank
     without such a reduction remains gauge data, while the bare prime character
     `p -> p^(1-2 Re rho)` merely encodes the target location and is a hidden-flow/RH reformulation.

## Log (cont. 43)

- 2026-07-10 — wave 41: classified the separate scalar FE and Schwarz gluing arrows on fixed and
  free zero orbits, proved their complete gauge trivialization and exact absence of a projective
  multiplier, and formalized factorization of every scalar gauge-invariant detector through orbit
  shape. Only the new module was compiled and axiom-audited; no project-wide lint or full build ran.

## Wave 42 — the scalar weld class cannot reduce the germ gauge

204. **Prime-character attack.** `[BRIDGE / REJECTED]` A common gauge on a prime-indexed family
     leaves pairwise prime ratios, but the canonical analytic ratio is the susceptibility character
     `p^(1-2 Re rho)`. It stores the target location directly; as a continuous character of the
     prime-log weld it is an exponential parameter, hence a hidden-flow/RH reformulation rather
     than an arithmetic constraint forcing the location.
205. **Full automorphism test.** `[PROVED HERE + Lean]` The existing upper symplectic shear is joined
     by the lower shear `(x,y) -> (x,x+y)`, which preserves every weld area form. These two fixed
     automorphisms are enough to test every proposed scalar orientation.
206. **No marked direction or scalar reader.** `[PROVED HERE + Lean]` A generator-plane vector fixed
     by both shears is zero. A real linear functional invariant under both shears vanishes on the
     two coordinate generators and is therefore zero. The conclusion holds for every conversion
     rate, including the degenerate zero class.
207. **Class-line exhaustion.** `[PROVED HERE + Lean]` Transport through the existing additive
     equivalence `weldClassLineEquiv` removes the rate coordinate: every natural marked vector and
     scalar reader attached to an arbitrary weld class vanishes. Even a reader family allowed to
     depend on the entire weld-class line is identically zero. Complete proof:
     `../2-fully-proven/new/weld-germ-orientation-no-go.md`.
208. **Combined scalar no-go.** `[PROVED NATIVE CONSEQUENCE]` Wave 41 kills invariants of the local
     scalar FE/Schwarz arrows; wave 42 kills a natural scalar gauge reduction from the global weld
     area. Thus the scalar route is exhausted from both sides. The weld class cannot repair the
     germ-gluing blindness by supplying an orientation.
209. **New open core.** `[OPEN CORE]` Work before the class-to-area collapse. Retain prime labels in
     a module with a lattice, filtration, or pairing whose gauge-preservation law is derived from
     the completed Euler datum. The obstruction must be non-character-valued: a freely chosen
     prime-log character either inserts arithmetic data or re-encodes the zero location.

## Log (cont. 44)

- 2026-07-10 — wave 42: subjected the proposed weld-to-germ orientation to the full symplectic
  automorphism group, proved the absence of natural marked vectors and scalar readers for every
  weld class and every class-dependent reader family, and combined it with wave 41 to close the
  scalar descent route. Only the new module and exact target were checked; no broad lint ran.

## Wave 43 — order-zero admissibility is exactly scalar germ gauge

210. **Existing filtration re-read.** `[PROVED INFRASTRUCTURE]` The differential-order filtration
     already supplies a marked scalar identity line and a principal-symbol quotient. The next open
     core is not to invent a filtration but to determine what an actual germ gauge can do inside it.
211. **Prop interface discharged exactly.** `[PROVED HERE + Lean]` Real scalar gauge families embed
     faithfully as cochains `g -> (0,r_g)`. They are automatically order zero, and conversely every
     `IsOrderZeroAffineCochain` is uniquely of this form. The admissibility Prop hides no additional
     cochain directions.
212. **Scalar primitive eliminated.** `[PROVED HERE + Lean]` For every nonzero rate, no arbitrary
     real scalar gauge family has boundary equal to the affine weld cocycle. Every prime
     specialization is hypothesis-free.
213. **Complex germ gauges eliminated at the size level.** `[PROVED HERE + Lean]` The canonical
     logarithmic-norm readout of any complex scalar gauge family remains in the scalar order-zero
     line and cannot trivialize a nonzero or prime weld. Complete proof:
     `../2-fully-proven/new/scalar-germ-gauge-weld-obstruction.md`.
214. **Local/global separation.** `[PROVED INTERFACE CONSEQUENCE]` Wave 41 supplies local complex
     normalizing scalars on both fixed and free orbit shapes; wave 43 proves that no scalar choices
     over all weld labels extend to a global weld primitive. Scalar coherence is impossible, not
     merely unconstructed.
215. **New open core.** `[OPEN CORE]` If a free completed zero orbit is to contradict the filtered
     weld, it must force a positive-order cochain whose principal symbol is exactly the derivation
     count `weldDerivSymbol`; scalar rescalings cannot do it. Derive or falsify that implication from
     the completed prime-action on the divisor jet, without a carrier or logarithm branch.

## Log (cont. 45)

- 2026-07-10 — wave 43: identified the entire order-zero cochain interface with actual scalar germ
  gauges, removed its admissibility hypothesis, ruled out real and complex-size scalar primitives
  at every prime, and isolated the positive-order symbol as the only possible global bridge. Only
  the new module and exact target were checked.

## Wave 44 — the forced positive-order primitive is locally boundary-blind

216. **Pinned positive-order realization.** `[PROVED INFRASTRUCTURE]` The natural local defect of an
     action on a torsion presentation is the commutator `sigma*A-A*sigma`; its Fitting boundary
     class vanishes identically.
217. **Full affine correction.** `[PROVED HERE + Lean]` Add arbitrary target factors `A*Hr`, source
     factors `Hl*A`, and arbitrary multiples of the local divisor equation on both sides. The
     combined defect still has zero Fitting boundary for every finite square presentation over any
     commutative ring.
218. **Universal nonrepresentation.** `[PROVED HERE + Lean]` Every nonzero Fitting boundary class is
     outside the entire commutator-plus-two-sided-factor affine family. Complete proof:
     `../2-fully-proven/new/pinned-affine-weld-boundary-no-go.md`.
219. **Filtered-weld consequence.** `[PROVED SYNTHESIS]` Wave 43 forces any possible weld primitive
     beyond scalar gauge to carry the derivation-count symbol. Wave 44 proves that realizing this
     positive-order part as a pinned commutator cannot activate a live local boundary, even after
     the full affine correction. Both natural pinned coefficient levels are closed.
220. **New open core.** `[OPEN CORE]` Define intrinsic nonlocality as a constraint class whose local
     restrictions are all commutator/factor-zero but whose completed boundary is nonzero. Do not
     realize it by constructing a carrier, cutoff evolution, or limiting transport.

## Log (cont. 46)

- 2026-07-10 — wave 44: combined commutator blindness with both source- and target-factor gauge
  blindness, formalized the universal pinned-affine vanishing and converse nonrepresentation
  theorem, and closed the natural local realization of the forced positive-order weld primitive.
  Only the new module and exact target were checked.

## Wave 45 — intrinsic nonlocality becomes a universal quotient class

221. **Pinned-affine subgroup.** `[PROVED HERE + Lean]` For every fixed torsion presentation, all
     commutator-plus-two-sided-factor defects form an additive subgroup of the full matrix defect
     group. Intrinsic non-affineness can therefore be expressed by a quotient, not by a carrier.
222. **Universal constraint object.** `[PROVED HERE + Lean]` Define
     `PinnedAffineDefectQuotient` by dividing defects by that subgroup. Every additive detector blind
     to pinned affine realizations descends through the generic `pinnedAffineBlindLift`.
223. **Fitting boundary descends automatically.** `[PROVED HERE + Lean]` The combined vanishing from
     wave 44 proves the full subgroup lies in the kernel of the bundled Fitting boundary homomorphism;
     no extra blindness Prop is assumed. The resulting `pinnedAffineBoundaryHom` is canonical.
224. **Live classes survive.** `[PROVED HERE + Lean]` Every defect with nonzero Fitting boundary has
     nonzero pinned-affine quotient class. The existing one-slot presentation `A=X^2`, `Delta=1`
     supplies an explicit nonzero class, so the quotient is not vacuous. Complete proof:
     `../2-fully-proven/new/pinned-affine-defect-quotient.md`.
225. **Dual-gate verdict.** `[PROVED NATIVE OBJECT]` The quotient construction is standard algebra;
     the new knowledge is the exact HGT subgroup, automatic descent of the seam boundary, and
     explicit nontriviality. “Intrinsically nonlocal” now names a universal constraint class.
226. **New open core.** `[OPEN CORE]` Construct a canonical completed prime--archimedean source map
     into `PinnedAffineDefectQuotient` without using analytic order, fixed/free orbit shape, a cutoff,
     or a character encoding the zero location. Its nonzero value must force new compatibility, not
     merely restate determinant transversality.

## Log (cont. 47)

- 2026-07-10 — wave 45: formed the subgroup of every pinned affine realization, constructed its
  universal quotient and generic detector lift, descended the Fitting boundary without a Prop
  hypothesis, and proved live-class survival plus explicit nontriviality. Only the new module and
  exact target were checked.

## Wave 46 — raw prime evaluation activates the quotient everywhere

227. **Canonical one-slot source model.** `[PROVED HERE + Lean]` For the order-`m` presentation
     `A=X^m`, the constant defect `C(c)` has Fitting boundary exactly the constant divisor jet
     `C(c) mod X^m`; the descended quotient boundary has the same value.
228. **Generic activation.** `[PROVED HERE + Lean]` For every positive order and every nonzero
     coefficient `c`, the constant defect has nonzero Fitting boundary and nonzero pinned-affine
     quotient class.
229. **Prime source is all-point nonzero.** `[PROVED HERE + Lean]` The obvious source
     `c=p^(-rho)` is nonzero for every positive base and every complex point `rho`. Hence its
     quotient class is nonzero with no hypothesis that `rho` is a zero or lies on either side of the
     critical line. Complete proof:
     `../2-fully-proven/new/pinned-affine-constant-source-blindness.md`.
230. **RH-interface verdict.** `[FALSIFIED]` Nonzero raw prime-to-quotient incidence cannot select
     zero location: it activates uniformly before the divisor or orbit constraints enter. The
     quotient remains a genuine obstruction recipient, but its mere nonvanishing is position-blind.
231. **Dual-gate verdict.** `[PROVED ACTIVATION NO-GO]` Constant-jet and complex-power facts are
     standard; the branch-level new result is the uniform activation classification of the new
     quotient, preventing a false RH interpretation.
232. **Finite constant-source collapse.** `[PROVED HERE + Lean]` Every finite family of constant
     sources enters the one-slot quotient only through its scalar total. Its quotient class is zero
     exactly when that sum is zero; all prime/source labels are forgotten.
233. **Pointwise cancellation is circular.** `[PROVED HERE + Lean]` At every point and for any two
     positive bases, two nonzero coefficients chosen from that point cancel the two-prime quotient
     class exactly. Such a cancellation law contains the target location in its coefficients and
     has no arithmetic force.
234. **New open core.** `[OPEN CORE]` A completed source must retain nonconstant germ information—at
     least higher prime-log jet coefficients—or infinite-support structure before the constant
     scalar collapse. Its cancellation must be arithmetically fixed and cannot be chosen from zero
     location, fixed/free orbit shape, or a cutoff.

## Log (cont. 48)

- 2026-07-10 — wave 46: computed the exact constant-source quotient boundary, proved nonzero
  activation for every nonzero constant, and showed prime evaluation activates at every complex
  point. The finite-source extension then proved exact collapse to one scalar total and exhibited
  pointwise-tuned two-prime cancellation as circular. This kills raw incidence and finite constant
  cancellation as RH selectors while preserving the universal quotient as a legitimate constraint
  recipient. Only the touched module and exact target were checked.

## Wave 47 — prime first jets survive the scalar-collapse wall

235. **First nonconstant source.** `[PROVED HERE + Lean]` The order-two truncated prime germ is
     `J_p(rho;X)=p^(-rho)(1-log(p)X)`. Its constant and linear coefficients are computed exactly in
     the polynomial source interface.
236. **Polynomial boundary fidelity.** `[PROVED HERE + Lean]` For an arbitrary one-slot polynomial
     source `P`, the Fitting boundary is exactly `P mod X^m`. Hence the descended quotient boundary
     retains both first-jet coefficients rather than collapsing them to one scalar.
237. **Two-prime Vandermonde rigidity.** `[PROVED HERE + Lean]` For distinct positive bases `p,q`,
     `a[J_p]+b[J_q]=0` in the order-two pinned-affine quotient iff `a=b=0`, uniformly for every
     complex point `rho`. Prime amplitude nonvanishing removes `rho`; `log p != log q` removes the
     labels. Complete proof:
     `../2-fully-proven/new/pinned-affine-prime-jet-rigidity.md`.
238. **Arbitrary finite-support rigidity.** `[PROVED HERE + Lean]` For any `k` injectively labelled
     positive bases, the first `k` derivative jets are independent in the order-`k` quotient at
     every point. Quotient vanishing gives the first `k` prime-log moment equations; the verified
     Vandermonde kernel theorem forces every source coefficient to zero. The prime specialization
     closes the full bounded-support jet tower.
239. **Location audit.** `[SURVIVES]` The theorem contains no xi-zero or critical-line hypothesis and
     holds everywhere. Unlike susceptibility, its rigidity is sourced by distinct prime logs, not
     by encoding `Re rho`.
240. **Dual-gate verdict.** `[PROVED NATIVE SURVIVOR]` Vandermonde elimination is standard; uniform
     finite-family survival inside the new pinned-affine quotient is the first label-sensitive
     source theorem after the constant-source no-go.
241. **Archimedean derivation outside every finite prime span.** `[PROVED HERE + Lean]` The fixed
     derivation moment sequence is `delta_(n,1)`. No finite packet of distinct positive prime-log
     evaluation characters realizes it: the zero moments in degrees `2,...,k+1` kill every packet
     coefficient by Vandermonde, contradicting the required degree-one value. This supplies an
     explicit non-finite-prime constraint without a limiting construction.
242. **New open core.** `[OPEN CORE]` Attach the archimedean derivation moment to
     `PinnedAffineDefectQuotient` through the completed prime--archimedean weld and derive the
     compatibility equation imposed on the infinite prime source. The attachment must remain fixed
     constraint data, not a limit flow, cutoff, or carrier.

## Log (cont. 49)

- 2026-07-10 — wave 47: moved from constant incidence to first prime-log jets, proved the exact
  polynomial boundary formula, uniform two-prime quotient independence, and the arbitrary
  finite-prime/order-moment Vandermonde theorem. It then proved the archimedean derivation moment is
  outside every finite prime span. This closes every bounded-support jet cancellation and supplies
  the first explicit fixed class on the completed side. Only the touched module and exact target
  were checked.

## Wave 48 — finite quotient completeness reverses the attachment verdict

243. **Weighted moment existence and uniqueness.** `[BRIDGE FORMALIZED]` Any `k` distinct characters
     with nonzero weights give a bijection from `k` amplitudes to the first `k` moments. Positive
     injective natural labels discharge distinctness for the negative prime-log frequencies, and
     complex prime amplitudes are nonzero at every base point.
244. **Finite-order prime blindness.** `[PROVED HERE + Lean]` Every coefficient vector in the
     order-`k` local divisor-jet algebra has a unique realization by any fixed square packet of `k`
     distinct positive prime derivative germs. Finite-prime independence therefore supplies a
     basis, not a separation from archimedean differential data.
245. **One-slot quotient classified.** `[PROVED HERE + Lean]` For the presentation `A=X^k`, the
     descended boundary `PinnedAffineDefectQuotient -> C[X]/(X^k)` is bijective. Its kernel is
     exactly the pinned-affine subgroup: the one-slot commutator vanishes and every remaining
     correction is precisely an `X^k` multiple. Every finite quotient class consequently has a
     unique representation by the fixed square prime packet.
246. **Earlier survivor verdict reversed.** `[FALSIFIED ROUTE]` No finite-order pinned-affine class
     can distinguish prime evaluation from an archimedean differential functional. In particular,
     attaching the derivation to a larger finite quotient cannot create arithmetic content; the
     prime packet spans that quotient completely.
247. **All-orders intersection theorem.** `[PROVED HERE + Lean]` If one finite prime-log packet agrees
     at every order with any eventually-zero differential moment sequence, then both are zero.
     Degrees `d,...,d+k-1` kill the prime amplitudes by a single shifted Vandermonde system, after
     which the full equality kills the differential sequence. The derivation sequence
     `delta_(n,1)` is now a corollary, not a special calculation.
248. **Constraint-side residue.** `[PROVED NATIVE DICHOTOMY]` Every finite truncation admits a unique
     prime realization, while no single finite packet realizes a nonzero finite-order differential
     sequence at all orders. The separating datum is cross-order compatibility itself. Choosing a
     new packet at each order is exactly the cutoff-carrier construction forbidden by the mission.
249. **Node-polynomial witness.** `[PROVED HERE + Lean]` For any nonempty family of negative real
     frequencies, the polynomial `Q(X)=prod_i(X-f_i)` vanishes at every node while `Q'(0)>0`.
     Therefore `k` negative evaluation characters cannot represent coefficient extraction at
     degree one through order `k`; distinctness of the nodes is not needed.
250. **Exact first omitted-order failure.** `[PROVED HERE + Lean]` For distinct positive labels,
     Vandermonde gives a unique packet matching the derivation moments in degrees `0,...,k-1`.
     The node-polynomial witness proves that this same packet fails at degree `k`. Thus each finite
     quotient succeeds exactly up to its own order and has an unavoidable next-order defect.
251. **Carrier test made algebraic.** `[PROVED CONSTRAINT CONSEQUENCE]` Repairing the defect by solving
     a new `k+1` packet changes all interpolation coefficients. Repeating that operation is a
     cutoff carrier in disguise; it is not an order-independent arithmetic source.
252. **New open core.** `[OPEN CORE]` Extract from the fixed Euler--Gamma datum one order-independent
     coefficient sequence and its functional-equation reflection law. Prove that the same
     arithmetic coefficients satisfy all truncations simultaneously, or identify a single
     arithmetic obstruction whose restrictions are the nonzero next-order defects. Neither the
     coefficients nor their support may be solved afresh at each order or chosen from a target zero.

## Log (cont. 50)

- 2026-07-10 — wave 48: proved weighted finite-moment existence and uniqueness, upgraded the local
  polynomial calculation to a bijective classification of the entire one-slot pinned-affine
  quotient, and showed every finite class has a unique prime-jet expansion. This reverses the
  earlier finite-jet survivor interpretation. The complementary all-orders theorem proves trivial
  intersection between finite prime packets and finite-order differential sequences. The sharper
  node-polynomial theorem proves the unique order-`k` interpolation fails at the first omitted
  order, making the cutoff-carrier diagnosis exact. The live datum is one fixed cross-order
  compatibility law. Only the edited module and exact target are checked.
