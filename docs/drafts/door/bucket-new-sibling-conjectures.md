# Bucket X7 — New sibling conjectures

**Bucket grade:** organizational (SEARCH channel). Sorted from `docs/support-extraction-log.md`.
**Scope (one line).** Genuinely-new candidate conjectures (the SEEDs) that are **not primarily owned by
G1–G5** — siblings, extensions, and low-prior "smell" candidates the user asked to mine for.
**Work package this seeds.** Pick the strongest live siblings (finite-free convolution flow,
motivic tower, regularization-freshness, erosion threshold) and promote each to a full draft brick with its own
Door passport. Several former siblings below are now banked as BRIDGE/structural results.

> **Grading discipline (the §42 trap, #68).** A SEED that is *merely RH-equivalent* is worthless; a
> SEED giving a **new explicit object or a non-trivial identity** is real. Each entry below is tagged
> **[REAL — new object/identity]** or **[RH-equivalent — needs an explicit hook]**. Numbering note: the
> log assigned `G6`/`G7` to *several different* conjectures across docs — treat the names below as
> labels, not a canonical numbering.

---

## Sibling families (non-circular, reject the fakes)

### Lee–Yang localization (#68 SEED-E, "candidate G7") — **[REAL, resolved BRIDGE]**
Banked as `lee-yang-localization.md` (#96): Kurasov–Sarnak / Lee–Yang crystalline forcing is an
interior mechanism, while arithmetic ζ is the Poisson/lattice degenerate point where forcing fails.
The result is a structural theorem: RH is marginal real-rootedness at the no-margin (`Λ_dBN=0 = λ_c=1
= κ₋=0`), not real-rootedness forced by crystallinity.

### FE = crystalline self-duality (#68 SEED-F, "candidate G8") — **[REAL, resolved BRIDGE]**
Banked as `fe-fourier-quasicrystal.md` (#97): FE is equivalent to theta/Poisson self-duality of the
integer Dirac comb, and the zeros↔primes face is the explicit formula. Door-2 verdict: classical
BRIDGE. Payoff: crystallinity is RH-blind; Davenport–Heilbronn is FE/crystalline but off-line, so the
separator is Euler genuineness plus archimedean polarization.

## What RH is *about* (intrinsic locus)

### Intrinsic RH locus = pure + polarized (#68 SEED-I §22, "candidate G9") — **[REAL, resolved BRIDGE]**
Every multi-q module has a native `ζ_M(s)=∏_p det(1−A_p p^{−s})^{−1}`; poles = trivial-`G_M`-rep
multiplicity; FE ⟺ polarization/self-duality; **RH meaningful-and-clean ⟺ pure + polarized.**
Banked as `intrinsic-rh-locus-pure-polarized.md` (#98): RH is ill-posed off the polarized locus and is
the `κ₋=0` positivity on it. The arithmetic-motives/Euler-cut identification remains the open apex.

## Homological / categorical

### Koszul-acyclicity (#73 SEED-R, #79 SEED-T, "candidate G15") — **[REAL — explicit `e–h` identity]**
The monoidality obstruction `ω ∈ H²(G_L)` (→ [[G4-multi-q-picard-vessiot-and-langlands-group]]) read as
**Koszul homology of the prime lattice in the `∏_p` limit**: *Conjecture:* "RH/Tannakian ⟺ no Koszul
homology condenses in the renormalized `∏_{p≤P}→∏_p` limit." Finite shadow = the `e–h` duality
`Σ_{i+j=k}(−1)^i e_i h_j=0` (**ledger-proven**, `EHKoszulDuality`); SEED-T: the operations λ-ring and
the cohomology grading are the **same Koszul complex** of the prime lattice. A homological "fourth
language" for the renormalization wall (alongside ξ-outer condensation, LP-survival, explicit-formula
limit).

## Transcendence siblings / extensions of G2

### Family-DSS = the Grand Simplicity Hypothesis (#69 SEED-N, "candidate G13") — **[REAL, resolved BRIDGE]**
Across primitive `L(s,χ)` the difference bases are **SHARED** (same primes `p`, only the twist `χ(p)`
differs), so family-independence is **NOT free** — a genuinely new obstruction (cross-resonance over
common primes). Banked as `family-dss-gsh.md` (#100): the alleged shared-prime obstruction splits by
unique factorization plus a finite cyclotomic/root-of-unity residue, so it is BRIDGE, not a new apex.
GSH is the family linear shadow of the same A2/F₁ value-lift apex.

### Tate–prime rigidity (#69 SEED-M, "candidate G12") — **[REAL, backbone banked]**
`P_k = [motivic ζ(k) part, imported MT(ℤ)] + [prime/Stieltjes a_j part, NO motivic home]`. *Conjecture:*
"the secular moment **rigidly welds** a known motivic block to an unknown prime block — that weld is the
new object no existing transcendence theory addresses." Banked as `tate-prime-rigidity.md` (#101) for
the non-split `K`-extension backbone (#117/#124); the general independence over `𝓡` remains DSS-cross.

### Regularization-freshness (#74 SEED-S, "candidate G16") — **[REAL]**
zeta-regularization / Hadamard-finite-part is a **transcendence-CREATING** operation (`log 2π=−2ζ'(0)`,
Glaisher). *Conjecture:* "the regularization constants of a hypertranscendental object are
transcendentally **fresh** relative to its periods — this freshness is the field's irreducible new
transcendence." (primary discussion in [[bucket-the-seam-archimedean-obstruction]])

### The live motivic period tower (#80 SEED-U) — **[REAL, resolved/corrected BRIDGE]**
The tower recurses **motivically, not spectrally**: `𝒫_𝒵=ℚ⟨P_k⟩` carries a motivic Galois action; the
"fixed point" = the pro-unipotent radical of its motivic Galois group. *Conjecture:* "the field has TWO
Galois towers — a dead spectral one and a live motivic one — and the seam is their non-interaction."
Falsifiable via Voros's explicit `𝒵(2m)∈{π,ζodd,Stieltjes}`.
Banked as `motivic-period-tower.md` (#102): the dead spectral tower stays dead by the First Theorem,
while the live tower is not mixed-Tate but exponential-motivic (`G^exp/K`), with `{γ_n}` in the wild
kernel layer.

## New native objects / coordinates

### The friable Dirichlet polynomial — the native auxiliary function (#71, object N5) — **[REAL — ledgered base]**
The field's native auxiliary-function space = **friable (S-smooth) Dirichlet polynomials**
`Σ_m λ_m n_m^{−s}`, `n_m=∏p^{m_p}` — *the* infinite-base Siegel–Shidlovsky auxiliary space (not a side
idea). Transcendence race (Prop 8.3) as its native theorem-shape; bridge to Granville–Soundararajan
"pretentious" territory. Ledger base: `boundedExponentVectorEquivSmooth`,
`diagonalAuxiliaryForm_eq_dirichletPolynomial`. (→ [[G2-multi-q-siegel-shidlovsky]])

### The finite-free convolution flow (#98 SEED-AB) — **[REAL — new coordinates, runnable test]**
The degree-d Jensen/secular section of Ξ evolves by the **finite free convolution `⊞_d`
(Marcus–Spielman–Srivastava)**: `Ξ_d^{(P)} = H_d ⊞_d K_d(p_1) ⊞_d …`, `⊞_d` preserves real-rootedness
(MSS interlacing). Since finite-free cumulants **ADD**, the criterion = a single **additive cumulant
sequence `κ_k=Σ_p κ_k(p)` staying in the real-rooted cone** (= the secular moments in disguise).
*Conjecture:* "RH = stability of the finite-free CLT fixed point under the additive arithmetic cumulant
drift." Replaces the open analytic LP-limit with an additive cumulant limit; imports MSS interlacing as
new tools. **Runnable test:** compare finite-free cumulants of `J^{d,n}` vs `Σ_p κ_k(p)`. (→
[[G5-unitarity-gatekeeper]] LP-limit face, [[bucket-realization-and-fake-family]])

## The no-margin as a threshold theorem (#67 SEED-B, "candidate G7") — **[REAL — exact identity]**
The pump `= L_∞(1)·Res_{s=1}ζ = (π^{−1/2}Γ(½))·1 = 1` **exactly** (`Γ(½)=√π`). *Conjecture:* "the single
positive direction has strength **exactly 1** (Tamagawa), and 1 is exactly the threshold for a second
positive direction" — the no-margin as a theorem about the archimedean continuation engine at the paired
seam points `{0,1}`. (→ [[bucket-the-no-margin]])

## The seam firewall (#67 SEED-A, "candidate G6") — **[RH-equivalent — needs hook, but structurally important]**
*Conjecture:* "the multiplicative (finite-place) Galois data and the archimedean continuation data are
difference-Galois-**independent** in the strip; no finite-place positivity forces the archimedean
positivity." If TRUE it sharpens why number-field RH is irreducibly harder than function-field RH (an
extra place); if FALSE (some higher `ind(D)` constraint survives) it would be a route to RH. *The
structural reason A1 is not free.* (closely related to [[bucket-the-seam-archimedean-obstruction]])

## The wild cells — adjudicated (#85, #70 B-stubs) — mostly **[RH-equivalent / FALSIFIED]**, kept for the record
- **B24 (a profinite Galois group acts on the zeros):** **FALSIFIED literally** (DSS ⟹ zeros
  transcendental ⟹ no finite Galois orbit). **Sharpened:** B24 = B8 (missing Frobenius) = DSS — three
  names for "number field ≠ function field." (→ [[bucket-the-seam-archimedean-obstruction]]) Over `F_q`
  it is TRUE (Frobenius). *The ABSENCE of B24 IS the missing Frobenius.*
- **B11 (transcendence ⟹ GUE):** family-DSS ⟹ random-matrix universality (reverses "statistics suggest
  structure"). couples A2 to spectral statistics. **[REAL — directional]**
- **B18 (Hilbert–Pólya transcendence obstruction):** banked as `hp-not-too-algebraic.md` (#108). The
  function-level no-ADE/holonomic obstruction is Hölder/hypertranscendence and BRIDGE; the value-level
  obstruction is exactly DSS and remains open. **[REAL, resolved/collapsed]** (→
  [[G5-unitarity-gatekeeper]])
- **B25 (continued carrier `𝒵(w)`):** RH = contour positivity of the meromorphically continued carrier =
  the continuous envelope of the discrete Li/Hankel Face A. **[RH-equivalent]**
- **B26 (transcendence creates the spectrum):** = the realization problem → [[bucket-realization-and-fake-family]].
- **B23 (transcendence tower):** dead spectrally, live motivically → SEED-U above.

---

## Triage for promotion (the work-package shortlist)
**Strongest [REAL] siblings to promote first** (new object/identity, non-circular, a runnable test or a
known toolkit to import):
1. **Erosion threshold** (G19, in [[bucket-time-and-non-holonomic-time]]) — gives `½` an intrinsic
   non-circular meaning; largely a theorem already.
2. **Finite-free convolution flow** (SEED-AB) — new coordinates, MSS toolkit, runnable test.
3. **Motivic period tower** (SEED-U) — live motivic tower after the spectral tower fails.
4. **Regularization-freshness** (SEED-S) — structural BRIDGE backbone exists, apex still open.
5. **No-boundary selection** (#195) — new variational selection axis; likely BRIDGE/D2 but not yet shaped.

## Cross-references
- [[G2-multi-q-siegel-shidlovsky]] — family-DSS, friable auxiliary, motivic tower extend it.
- [[G5-unitarity-gatekeeper]] — Lee–Yang, FE-crystalline, finite-free, B18 feed it.
- [[bucket-the-seam-archimedean-obstruction]] — Tate–prime rigidity, regularization-freshness, seam firewall.
- [[bucket-realization-and-fake-family]] — B26 realization, finite-free identification.
- [[bucket-time-and-non-holonomic-time]] — the erosion threshold (the strongest native sibling).
