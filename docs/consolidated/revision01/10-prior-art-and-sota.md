# 10 — Prior-art / SOTA map (what is already known — stop rediscovering)

> Purpose: pin where this program's apparatus is **classical/known**, so effort goes only to genuine open
> cores and we stop re-deriving textbook results. Register: `[KNOWN — cite]` for located prior art,
> `[NOT FOUND]` for cells a literature sweep did not turn up (candidate non-reducing, *verify before
> claiming*). Method: six-cluster WebSearch + arXiv sweep (2026-06-22), adversarially spot-checked; the two
> most load-bearing "we rediscovered this" references (Derkach–Hassi–de Snoo 2002, Uvarov 1969) verified
> directly. Citations are as located in the sweep; items marked `[unverified]` were not independently confirmed.

## A. Classical — our objects are textbook/known (cite, do **not** re-derive)

1. **Reciprocal-square zero power sums `T_k=2Σ_{γ>0}γ^{−2k}` are the Voros secondary (super)zeta values `Z(2k)`.**
   `[KNOWN]` Mellin 1917; A. Voros, *Zeta Functions over the Zeros of Zeta Functions*, Springer LNM (2010);
   Voros, arXiv:1403.4558 (an "exponential-asymptotic view of RH" — echoes our exponent law). These are
   well-known computable constants. *We invented no new moments.*

2. **`Q_0[p]≥0 ∀p,d ⟺ RH` is a moment-positivity criterion in the known Weil/Li/Csordas–Varga family.**
   `[KNOWN — shape]` Weil 1952 (explicit-formula functional positivity); Li 1997 + Bombieri–Lagarias,
   *J. Number Theory* 77 (1999) 274 (`λ_n≥0`, = discretized Weil positivity); **Csordas–Varga, "Moment
   inequalities and the Riemann hypothesis," *Constr. Approx.* 4 (1988) 175** — the closest precedent
   (moment-positivity for RH, but integral moments of `Φ`, not discrete zero-moments). **Low-content caveat:**
   for *any* positive measure the `T_k` Hankel matrix is automatically PD, so `H^0⪰0` carries no content by
   itself — `Q_0≥0⟺RH` is the Hamburger moment problem detecting *real support* = "the zeros are real,"
   repackaged in a new coordinate. The specific assembly `[T_{i+j+1}]` of Voros constants was *not* found
   verbatim, but it follows from standard moment-problem logic. `[NOT FOUND verbatim, but reduces-to-known]`
   **The `Q_0≥0 ⟹ RH` half is now rigorously written down (gpt/proof12 = bridge T30):** Hamburger + the Cauchy-transform
   singularity structure (a positive real-line measure's transform is holomorphic off `ℝ`, so non-real divisor poles
   are impossible) + Weierstrass uniqueness. It **passes the roleplaying audit** (a precise checkable reduction, not a
   crossing of the wall; proof12 §5 says so itself) but is **low-novelty classical moment theory** — exactly the `⟹`
   half of this known family. The hard `⟸` (source-built `Q_0≥0`) is untouched = the open apex.

3. **`s_d` = inverse Christoffel function = ratio of Hankel determinants.** `[KNOWN — textbook]`
   Szegő, *Orthogonal Polynomials* (AMS, 1939); Nevai, *J. Approx. Theory* 48 (1986) 3–167; Simon,
   "The Christoffel–Darboux kernel," arXiv:0806.1528. **comp80 reduces-to-known** (see §06 honesty note).

4. **The Christoffel/Uvarov one-point boundary-removal kernel (= proof11) is Uvarov's 1969 formula.**
   `[KNOWN — classical]` V.B. Uvarov, *USSR Comput. Math. Math. Phys.* 9 (1969) 25; Hankel-determinant form
   in Krattenthaler, arXiv:2103.03969; modern Darboux re-derivations Kozhan–Vaktnäs arXiv:2407.13961.
   **proof11 re-derived a 1969 formula** — keep as scaffolding, cite Uvarov, claim no novelty.

5. **Rank-one moment-matrix perturbation + Sherman–Morrison kernel update.** `[KNOWN — classical applied]`
   Woodbury 1950; OP-specific use in arXiv:1601.07194. A textbook combination of A3 + A4.

6. **Generalized Nevanlinna `N_κ` / Krein–Langer `Π_κ`, and the rank-one `Π₁→Π₀` transition.**
   `[KNOWN — the abstract theorem exists]` Krein–Langer (1970s–80s); **Derkach–Hassi–de Snoo, "Rank one
   perturbations in a Pontryagin space with one negative square," *J. Funct. Anal.* 188 (2002) 317–349**
   (verified) — the abstract theory of negative-square-count change under rank-one perturbation. Truncated
   `N_κ` moment problems: Derkach–Hassi–de Snoo, arXiv:1101.0162. **proof10's `N₁` carrier theorem is the
   ζ-specialization of DHdS 2002, not the abstract transition.** Open action: compare DHdS's scalar
   negative-square-jump condition to our gap `s_d>0`; if they specialize differently, *that divergence* would
   be the only load-bearing new content here.

7. **RH as positivity of a canonical-system / Hamiltonian (boundary-Weyl positivity) is already published.**
   `[KNOWN]` Suzuki, arXiv:1204.1827 (RH ⟺ Hamiltonian positive-semidefiniteness); Lagarias arXiv:1606.05726;
   Burnol; Remling. Our "rank-one boundary-Weyl bridge" overlaps this framing — check `s_d` against Suzuki's
   Hamiltonian positivity before claiming the boundary-Weyl view as new.

8. **de Branges positivity conditions FAIL for ξ — a documented no-go.** `[KNOWN — heed]`
   Conrey–Li, "A note on the de Branges approach…," *IMRN* 2000(18) 929, arXiv:math/9812166. Any de-Branges /
   positivity route for ξ must state explicitly why it escapes this failure (or concede it reduces).

9. **Pólya–Jensen / Turán / de Bruijn–Newman — distinct from our `T_k` Hankel.** `[KNOWN]`
   Pólya 1927; Griffin–Ono–Rolen–Zagier, *PNAS* 2019, arXiv:1902.07321 (*asymptotic* hyperbolicity only —
   not full RH); Rodgers–Tao, arXiv:1801.05914 (`Λ≥0`); Csordas–Norfolk–Varga 1986 (degree-2 Turán). These act
   on ξ's **Taylor coefficients** — a *different* sequence from our zero power sums. Do not conflate (the
   earlier "Jacobi–Krein ↔ Pólya–Jensen are one object" framing was wrong; corrected in §06).

10. **Hypertranscendence theory is mature but fragmented.** `[KNOWN]` Hölder 1887 (Γ); Ostrowski 1920 (ζ);
    difference-Galois: Hardouin–Singer arXiv:0801.1493, Adamczewski–Dreyfus–Hardouin (ADH) 2021 arXiv:1910.01874;
    motivic: Fresán–Jossen, *Exponential Motives*. Joint ζ/Γ differential independence: arXiv:1811.04188/1811.09336.
    "Fixed by a constraint, not propagated by a flow" is **framing, not theorem** (the Galois framing is "the
    differential Galois group is large"). **Any specific HT result almost certainly reduces to ADH 2021 — check
    there first.** (Matches the program's own "mature-fragmented" finding.)

11. **Davenport–Heilbronn as FE-but-not-RH witness; the Euler product as the separator.** `[KNOWN]`
    Davenport–Heilbronn 1936; Selberg class (Selberg 1992; Kaczorowski–Perelli); Saias–Weingartner; Righetti
    arXiv:1412.6331; Booker arXiv:1306.6362. "Euler product + functional equation ⟹ RH" is open / essentially
    RH-equivalent.

12. **The Connes–Consani(–Moscovici) archimedean-positivity programme — the SOTA our "source-built faithful-index"
    language circles `[KNOWN — flagged by gpt/45, verified]`.** "The likely proof object is archimedean, source-built,
    positivity/polarization, not prime-flow" is *aligned with existing SOTA, not a private discovery*. Key bodies:
    the **arithmetic site** (Connes–Consani, *Adv. Math.* 2016); the **Riemann–Roch theorem for the Arakelov
    compactification of Spec ℤ** (Connes–Consani, ~2023) and the "Jacobian of $\overline{\mathrm{Spec}\,ℤ}$" (preprint
    ~2026); and especially **"Zeta zeros and prolate wave operators"** (Connes–Consani–Moscovici, arXiv:2310.18423 =
    *Ann. Funct. Anal.* 15(4):87, 2024; PNAS "The UV prolate spectrum matches the zeros of zeta," 2022). **Direct
    structural overlap with our battery:** the prolate operator is "the **square of the scaling operator** + the
    **grading of orthogonal polynomials**," with a **positive/negative (Sonin-space) spectral split** — i.e. an
    archimedean, OP-graded, one-sided-positivity object. Our Christoffel/`N₁`/`s_d` apparatus is adjacent to this.
    *Action: compare our `s_d`-gate / `Π₁` split directly against the prolate positive/Sonin split before claiming any
    boundary-Weyl novelty; the semilocal trace-formula positivity is the same family.* (Connes, arXiv:2602.04022,
    "RH — Past, Present and a Letter," 2026, is the latest survey.)
    **Comparison done `[no-roleplay-items §5, 2026-06-22]`:** the prolate operator is `W_λ=−𝕊²+2πλ²(4N+1)−¼` (`𝕊`
    scaling, `N` Hermite/OP grading; Sonin = negative eigenvalues `~γ_n²`). Our **archimedean protector lattice
    `2|w|=4N+1` (N≥0) IS the prolate Hermite grading** (verified exact: N=0 the `s=1` pole/`−4` term, **N=1 the boundary
    atom `a_*=0.16`**), same Gaussian origin (`Γ_ℝ`=Mellin of the prolate cyclic vector). BUT the literal "compression"
    claim is **false**: the cited Sonin compression proves Weil positivity at the archimedean place *unconditionally*,
    while `s_d>0` is RH-conditional — so `a_*` (= `M_triv`, unconditional) matches the *archimedean* prolate, whereas
    the prime demand `a_c(d)` (the finite places) is outside it. Corrected target: `s_d>0` ↔ the **semilocal** prolate
    positivity (arXiv:2310.18423).

## B. NOT found in the sweep — candidate non-reducing cells (verify before claiming)

1. **Exterior hard-edge Christoffel asymptotic, explicit product `s_d ~ ∏_{j≤d} γ_j^{−α}` (comp49 / gpt/proof4).**
   `[RESOLVED — NOT open; reduces-to-known. Stahl–Totik chase done 2026-06-22.]` The verdict: **this is the
   non-regular regime of Stahl–Totik regularity theory — a derivable special case, not a frontier problem, with no RH
   content.** The reasoning, confirmed by literature (Totik, *J. d'Analyse* 81 (2000) 283; Stahl–Totik, *General
   Orthogonal Polynomials*, CUP 1992; Lubinsky 2009):
   - For a **regular** measure on a compact set, the exterior Christoffel function grows **purely exponentially**,
     `K_d(y_*,y_*) ~ exp(2d·g_E(y_*))` (Green's function of the complement). Classical.
   - Our measure `ν'=Σ_j 2γ_j^{−2}δ_{γ_j^{−2}}` is **NON-regular**: it is purely atomic on a thin set accumulating at
     the hard edge `0`, with super-polynomially decaying masses, and the `n`-th-root test **fails** — `K_d^{1/d} ~
     exp(α·ln d) → ∞` (super-exponential `~d^{αd}`, since `Σ_{j≤d}ln γ_j ≈ d ln d`), not the finite `exp(2g)` of the
     regular case. So Stahl–Totik's universal exterior law **does not apply**; for non-regular measures the exterior
     rate is **measure-specific** (the general/discrete-measure literature gives only *interior/on-support*
     asymptotics, no universal exterior rate). Hence no named theorem covers our product — and none should be expected.
   - It is nonetheless **elementarily derivable** (proof4 essentially does it): the minimizing polynomial kills the `d`
     dominant atoms, `q(y)≈∏_{j≤d}(y−x_j)/(y_*−x_j)`, giving `λ_d≈2x_{d+1}∏(x_{d+1}−x_j)²/a^{2d}`, hence
     `ln s_d ≈ −4Σln γ_j − 2d ln|y_*| + 4(1−ln2)d` = proof4's `α≈4+[4(1−ln2)+2ln|y_*|]/L̄_d`. A routine (if delicate)
     hard-edge interpolation computation — "unwritten for this measure," **not** a hard open problem.
   - **No RH content** (as our own docs already state): the no-margin *rate* is generic hard-edge geometry; the RH
     content is the *sign* `s_d>0`, not the rate. ⟹ **drop this as a novelty candidate.** (The non-regularity of the
     zeta-zero measure is a true but RH-empty consequence of the zeros being log-thin.)

2. **A *positivity*-framed Euler-product-vs-DH separator (the `s_d>0` gate).** `[NOT FOUND — = the open apex]`
   The standard separation is *multiplicativity* (Euler-product axiom), **not** positivity; a positivity gate
   that genuine Euler-product `L` pass and DH fails was not found formalized. This is exactly our open apex
   (source-built `s_d>0 ∀d`), which is itself RH-equivalent and open. *If* this gate is genuinely
   non-reducing, the content lives entirely here — not in the surrounding (classical) construction.

3. **Specific coordinate / identification.** `[coordinate, not theorem]` The seam-squared coordinate
   `y_ρ=−(ρ−½)^{−2}` returned zero hits; the rank-one Γ-atom = the `j=1` trivial-zero term at `y_*=−0.16`.
   These are a coordinate choice + explicit-formula bookkeeping, not new theorems.

## C. What this means for effort (the operational point)

- **Import, don't re-derive:** Christoffel variational/Hankel/RK identities (A3), Uvarov one-point modification
  (A4), Sherman–Morrison moment update (A5), the rank-one `Π₁→Π₀` transition (A6), Voros moments (A1). proof10,
  proof11, comp80 are **specializations/re-derivations** of A6/A4/A3 — keep as scaffolding with citations, claim
  **no** novelty for them.
- **The only genuinely-open, genuinely-significant target is the apex (B2):** the source-built `s_d>0 ∀d`
  (equivalently: why the Euler product passes the positivity gate and DH fails it). Everything else in the
  battery is classical apparatus reassembled in the seam coordinate.
- **Heed the no-go (A8):** Conrey–Li killed a de-Branges positivity route for ξ; state why ours differs.
- **B1 is now CLOSED (Stahl–Totik chase done):** the exterior-Christoffel asymptotic is the *non-regular* regime of
  Stahl–Totik theory — a derivable special case (proof4's interpolation argument), measure-specific, with no RH
  content. Not a novelty candidate; do not pursue it as OP theory. So **B2 (the apex `s_d>0`) is the sole open
  RH-bearing cell**, full stop.

## D. Independent convergence (gpt/45) and the line between scaffolding and new mathematics

A second, independent SOTA assessment (gpt/45, same task) reaches the **same bottom line** as the six-cluster sweep:
this is *a computationally driven candidate normal form / coordinate atlas of one known wall*, **not yet new
mathematics**. Convergent verdicts: "RH is positivity" is old (Weil/Hilbert–Pólya/de Branges/Laguerre–Pólya/Hankel/
Krein-index); the Jensen–Pólya route is SOTA (GORZ); the `s_d` identities are mechanical (Sherman–Morrison/Schur/
Uvarov/Christoffel) once the rank-one split is written; "bare primes are not enough" (comp73) confirmed an *expected*
failure mode, not new theory.

**Honest re-grading of the paper-math (gpt/45's self-correction — matches our `[conditional]` flags).** proof7–11 are
**algebraic consequences of assumed objects, not the source-built object itself**: the Green-identity/boundary-triple
language is plausible form but *not a constructed operator domain*; the finite-part regularization says what a
construction would need, not the canonical construction; the `N₁` carrier theorem (proof10) is **conditional on the
one-dimensional seam boundary quotient**; the determinant/τ identity (comp80) is real finite algebra that does **not**
prove `s_d>0`; the Christoffel kernel identity (proof11) is standard projection algebra, **not** an RH step; the gauge
law (proof9) only fixes extraction ambiguity. Keep all of it as scaffolding; claim none of it as a proof.

**The five statements that would actually be new mathematics (none yet achieved):**
1. a **source-built** derivation of `H^-` from the completed explicit formula *without zero-feeding*;
2. a proof that the signed object is `N₁` **from source data** (not assuming the 1-dim seam quotient);
3. a proof of the Γ/Uvarov repair positivity **`s_d>0 ∀d`** (the apex);
4. a theorem identifying the determinant/τ `s_d` with a known **Jensen/Pólya** object *in a positivity-preserving
   way* (note: comp80's identification is NOT positivity-preserving and is classical — see §A2/A3);
5. a **fake-family separation theorem**: precisely why Euler-product `L` keep `s_d>0` while Davenport–Heilbronn-like
   fakes cross `s_d=0` (= §B2, the candidate non-reducing cell).

**The concrete deliverable that would convert atlas → research output** (no RH proof required): a short note,
*"The reciprocal-seam moment form of ξ and its Γ-Uvarov boundary scalar,"* containing only defensible content —
define `y_ρ=−(ρ−½)^{−2}`, `T_k`, `Q_0`; prove `Q_0≥0 ⟹ RH` for the folded divisor; the gauge law
`T_k↦T_k+2k(−1)^{k+1}a_k`; the rank-one identities `H^0=H^-+a_*v_*v_*^T`, `s_d=a_*+1/m_d=1/K_{ν'}(y_*)=−det H^0/det B`;
the explicit statement that `s_d>0 ∀d` is RH-equivalent and **open**; reproducible computations (ζ, real Dirichlet,
complex self-dual products, DH crossing at `d*=62`, gauge audit, hard-edge fake controls, universal dip, μ_E nodes);
and a **direct comparison against GORZ and Connes–Consani**. That is real output as a precise finite normal form +
falsification ledger — the project's genuine contribution — explicitly short of a proof.

## E. Lens status against SOTA (does the map survive the sweep?)

The lenses (big-picture §1) are framings/projections, **not theorems**. The 2026-06-22 sweep **invalidated none
of them logically**; it relocates four as SOTA-overlapping (valid framings, not discoveries). (A *different* earlier
eighth lens — the empirical weld carrier — was retired as an analytic-continuation diagnostic and removed; the current
lens 8 below is the methodological *anti-mirror* lens, added 2026-06-22.)

| Lens | Status | Reading after the sweep |
|------|--------|--------------------------|
| 1 — Constraint, not flow | **stands** (framing) | = "the differential Galois group is large" (Hardouin–Singer / ADH); a heuristic, not a theorem; already scoped as such |
| 2 — Transport, not amplitude | **stands** | reframing of the explicit-formula log-derivative `ξ'/ξ=A+P`; valid, not novel |
| 3 — Weld and seam (two sources) | **stands — OVERLAPS SOTA** | the standard adelic archimedean/finite-places split; = the **Connes–Consani semilocal weld** |
| 4 — Faithful index `κ₋=0` (RH lens) | **stands — CORROBORATED, but a MIRROR (lens 8)** | = Krein–Langer `N_κ` integer index; comp72/81 confirm; load-bearing — *but RH-equivalent, so a relabel of RH, not a lever on it* |
| 5 — Two orthogonal axes (`ω=0⇏RH`) | **stands — = consensus** | the Selberg-class fact (FE alone ≠ RH; the Euler product separates); Davenport–Heilbronn is the standard witness |
| 6 — Affine confinement (passport) | **stands** (internal schema) | project-specific RH-blindness heuristic; not in the literature, not invalidated |
| 7 — Missing single Frobenius (value/Schanuel) | **stands — OVERLAPS SOTA; the one non-mirror direction** | the `𝔽₁` / function-field-analogy aspiration (Weil; Connes–Consani arithmetic site); Baker proven / Schanuel open. The *orthogonal* (value/transcendence) axis — not an RH-equivalent restatement |
| 8 — No target, only byproduct | **methodological constraint** (the anti-mirror / enforcement of lens 1) | RH-equivalence is horizontal/cheap (proof12); the difficulty is invariant under it. The *only* RH-type success (Deligne over `𝔽_q`) was a byproduct of building cohomology, not a direct attack. Rule: drop any RH-reducible target; build a non-equivalent constraint and let RH be the residue |

**Net.** The map survives as a correct re-drawing of known territory, not a set of new results. **Lens 8 reclassifies
the whole positivity column (lenses 3,4) as a *hall of mirrors*** — correct relabelings of RH that cannot lever it.
The SOTA it is closest to is **Connes–Consani**; the one genuinely-*different* (non-mirror) direction is **lens 7's
value/transcendence axis**. The redirection: stop polishing the positivity mirrors (`κ₋`/`s_d`); build the
*non-RH-equivalent* constraint (hypertranscendence / `𝔽₁` / transcendence-independence) from which the divisor's
location — hence RH — falls out as a byproduct.
