# Denied-Corpus Extraction Log

**Purpose.** A systematic mining of every document in `docs/denied/` for two things, per the
gatekeeper-conjecture program in `docs/drafts/00-foundations-native-objects-and-gatekeepers.md`:

- **(SEED)** — information that could support **creating a new conjecture** for the branch
  (hypertranscendental / non-holonomic functions, anything *related to time / non-holonomic time*,
  a natural **sibling** of an existing gatekeeper G1–G5, or anything with the right native "smell").
- **(SUPPORT)** — information that could **support an existing gatekeeper** (G1–G5) or help turn it
  into a theorem (a lemma, a reduction, a known result to cite, a proof strategy, a numerical certificate).

**Method.** One section per denied file. Each file is read *fully* into context, then mined. Findings are
recorded with air-marks: *Unverified* / *Conjecture* / *Import (classical)* / *Metaphor*.

**The existing gatekeepers (targets), for reference:**
- **G1** — Difference Hölder (KEYSTONE/C5): ζ satisfies no single algebraic q-difference equation.
- **G2** — Multi-q Siegel–Shidlovsky: trdeg = G_L-orbit dim ⟹ LI of zeros.
- **G3** — Holonomy dichotomy: holonomic ⟺ corank(Λ)<∞ ⟺ flat connection.
- **G4** — Multi-q Picard–Vessiot correspondence (autonomy/C7).
- **G5 (candidate)** — Unitarity gatekeeper: non-integrable multi-q connection has unitary holonomy on the
  σ-fixed locus ⟺ spectrum real ⟺ RH. (The bridge that would unify "time" with "RH-byproduct".)

**Two guiding assumptions the seeds are scored against:** A1 = RH becomes a natural byproduct;
A2 = the core tells us something about *time*.

---

## [#67] infinite-base-difference-galois-for-L-functions.md  — founding draft

**Grade:** EXTRACTION-PENDING (founding). High yield — this is the source of the gatekeeper statements.

### SUPPORT — G1 (difference Hölder, the keystone)
- **§18 (Brick #11) is the sharpest support for G1 and gives a proof *mechanism*.** A single Euler
  factor `f=(1-x)^{-1}` under the dilation `σ_q: x↦qx`, `q=1/p`, satisfies a *genuine first-order linear
  q-difference equation*: `f(qx) = (1-x)/(1-qx)·f(x)`. So each prime *individually* is q-difference-algebraic
  (group ⊂ 𝔾_m, abelian — vindicates Brick #2). The draft's own reading of G1: **"ζ has no *single* difference
  equation because it needs *all* dilations q_p=1/p at once — and that simultaneity is the Euler product = unique
  factorization."** *Proof strategy this hands G1:* difference-Hölder is not "no q-difference structure" (each
  factor has one) but "**no single dilation q amalgamates the infinitely many q_p=1/p**"; the obstruction is the
  ℚ-independence of `{log p}` (FTA). *Air: the single-factor equation is a real computation; the global
  no-single-equation is the conjecture G1.*
- **The ledger already proves the core obstruction (Tier-A A4):** `{log p}` is ℚ-linearly independent, via
  unique factorization (`Nat.factorization`), formalized as `Core`/`logPrime_no_rat_relation`. This is the
  rigorous floor under G1's "needs all q_p at once."

### SUPPORT — G2 (multi-q Siegel–Shidlovsky)
- **§4 and §16-Wing-B(b) state G2 verbatim** ("trdeg{γ_n} over the period field = dim of G_L-orbit; G_L ⊇
  𝕋^∞⋊ℤ/2 infinite-dim ⟹ LI"). Source for the gatekeeper text.
- **Brick #3/#8 give the *free half*:** the diagonal flow's pro-algebraic closure is all of `𝕋^∞` (Weyl + FTA,
  *not* Baker for the qualitative closure). So `dim G_L-orbit = ∞` is FREE; the hard part is *trdeg of the
  intersection points*, i.e. the zeros. This factors G2 into [orbit dimension: free] + [trdeg = orbit dim: the
  conjecture]. *Air: closure=𝕋^∞ is computed; the trdeg equality is open.*
- **Critic caveat (§10):** Baker survives in the *effective/Diophantine* rate (how fast the diagonal approaches
  the boundary zero-variety) — the quantitative coupling. So G2's hard column = "zeros **and** effective
  flow-rate at the boundary."

### SUPPORT — G3 (holonomy dichotomy / corank)
- Brick #3 free/hard table is the corank dichotomy in action: flow (corank-trivial part) free; zeros
  (corank-∞ part) hard. The "holonomic ⟺ flat" face appears as the multiplicative wing being the *solved/flat*
  half.

### SUPPORT — G4 (multi-q Picard–Vessiot)
- §18, §19-D1 name **multi-q Picard–Vessiot theory** as the central open object; single-factor PV group ⊂ 𝔾_m
  is the base case. "Multi-base q-difference Galois is genuinely open" — the autonomy target.

### SUPPORT / SEED — G5 (unitarity, the localization gatekeeper) — STRONGEST FIND
- **Lemma 1 is the native home of G5 (a real computation, not conjecture):** the FE `σ:s↦1-s` acts on every
  prime coordinate at once as inversion-and-scale `x_p ↦ p^{-1}x_p^{-1}`; its **fixed-*modulus* locus is exactly
  the critical line** `|x_p|=p^{-1/2} ∀p ⟺ Re s=½`. So **RH = "every zero lies on the σ-fixed-modulus locus of
  the infinite-base difference system."** This is precisely the locus on which G5's "unitary holonomy / preserves
  a norm" should be stated. *Air: Lemma 1 derivable (verified computation); the localization is RH.*
- **The draft already poses G5 nearly verbatim** (§10-Critic Brick #6-next): *"is the boundary action of σ⋉𝕋^∞
  **unitarizable** on the Nyman–Beurling space?"* and *"does the σ-inversion make the boundary dilation generator
  self-adjoint in the H²(𝕋^∞) metric?"* — i.e. G5 = "the σ-fixed locus carries a unitary (self-adjoint
  generator) structure ⟺ RH." Confirms G5 is the right localization gatekeeper and that it is *already named* in
  the corpus.

### SEED — new conjecture candidates
- **(SEED-A, seam-firewall) §17 Brick #10:** *Ramanujan ⇏ GRH* — the seam is a **positivity firewall**:
  multiplicative-wing positivity (Ramanujan, often proven, e.g. Deligne) transmits *no* constraint across the
  seam to archimedean-wing positivity (GRH). Candidate native conjecture **G6 (seam firewall):** "In the
  multi-q module, the multiplicative (finite-place) Galois data and the archimedean continuation data are
  difference-Galois-*independent* in the strip; no finite-place positivity forces the archimedean positivity."
  *If TRUE* it sharpens the independence (explains why number-field RH is irreducibly harder than function-field
  RH = has an extra place); *if FALSE* (some higher ind(D) constraint survives, §16 B.iii) it would be a route to
  RH. Either is a real result. **Smell: native (multi-q seam), and it is the structural reason A1 is not free.**
- **(SEED-B, no-margin exactness) §12 Brick #8-Critic:** the pump `= L_∞(1)·Res_{s=1}ζ = (π^{-1/2}Γ(½))·1 = 1`
  **exactly**, by `Γ(½)=√π`. Candidate conjecture **G7 (no-margin = threshold):** "the single positive
  direction has strength exactly 1 (Tamagawa), and 1 is *exactly* the threshold for a second positive direction"
  — the no-margin as a theorem about the archimedean continuation engine at the paired seam points {0,1}.
  *Smell: archimedean, ties to G5 positivity; the "no-margin" is FE-forced.*
- **(SEED-C, function-field model) §15/§17:** function field has **no archimedean place** ⟹ its RH = Ramanujan
  = Deligne (proved by geometry). This is the **faithful-restriction proving ground** (charter Door-5): G5 and
  G1–G4 should be *proved first over F_q(t)* where the archimedean wing is absent and Weil II is available. Then
  the number-field obstruction = exactly the archimedean wing = the missing Frobenius / F₁. *Smell: native border
  N4; concrete proving ground for all gatekeepers.*

### TIME (A2)
- **§19-D5:** "the diagonal Kronecker flow on `𝕋^∞` … the flow as the system's **'time.'**" The dense flow
  `t↦(p^{-it})_p` is literally the system's time evolution — and it is *free* (unique factorization). Combined
  with G1 (no single difference equation ⟹ no single discrete clock), this is the native content of A2: **the
  multiplicative wing supplies a free, dense "time" (the Kronecker flow); the zeros are what this time *cannot*
  reach without the archimedean wing.** Native seed for "non-holonomic time = the flow whose closure is free but
  whose fixed points (zeros) are not."

## [#68] multi-q-difference-galois-foundations.md  — the discipline's "city"

**Grade:** EXTRACTION-PENDING (the large foundations). **HIGHEST YIELD of the whole corpus.** This is the document
that *already contains, and in several cases proves*, the gatekeepers of `00-foundations`. The single most important
finding of the entire mining exercise is here: **G1, G3, G4 are largely already proved (in the difference category /
structurally) inside this denied document** — which directly bears on the charter's "0 proven native theorems" verdict.

### ⚑ HEADLINE — the gatekeepers G1–G5 are this document's conjecture ledger C1–C7, and several are PROVED
The drafts/`00-foundations` gatekeepers map onto this file's **conjecture ledger (§46)** with proof-status:
- **G1 (difference Hölder) = C6-converse for Λ=0 (§59), PROVED in the difference category.** §59.1 Galois-dimension
  argument: a holonomic diagonal ⟹ finite-dim s-difference-Galois group; but the arithmetic s-monodromy `g=(p^{-1})_p`
  has *infinite-dimensional* Zariski closure when `Λ=0` (unique factorization) ⟹ contradiction ⟹ ζ (and every
  arithmetic L, all `Λ=0`) satisfies **no finite-order linear difference equation** = difference-hypertranscendental.
  *Caveat (§61.3, self-correction #15):* this is the **difference**-category Hölder; *literal differential* Hölder for
  ζ is imported (Hölder 1887), and for general L is conjectural (reducible via Adamczewski–Dreyfus–Hardouin). **So G1
  as "no single algebraic q-difference equation" is essentially proved here**; G1 as "no differential equation" is
  Hölder (import) for ζ. The single-q version is supported by §51.1 (finite single-σ q-difference groups are *cyclic*,
  but the arithmetic object needs the full pro-torus 𝕋^∞).
- **G2 (multi-q Siegel–Shidlovsky) = C3.** PROVED on **CM ∪ tori ∪ F_q(t)**: Papanikolas 2008 proves the *full*
  statement `trdeg(periods)=dim G_M` over `F_q(t)` (§33, by exactly the field's mechanism — a σ-difference-Galois
  group computing transcendence); Wüstholz/Chudnovsky/Cohen–Shiga–Wolfart give the CM locus (§58); §43.2 gives tori.
  *The ℚ-gap is named exactly:* the **missing single Frobenius / infinite base** (§33.3, §34). §61–62 caveat
  (self-correction #16): on the *arithmetic* torus, `trdeg=dim` is **open** (Schanuel-type alg. independence of
  `{log p}`); only the *orbit dimension / torsor* (de Rham side) is elementary. So G2's hard half = the Grothendieck
  period conjecture for the non-CM/arithmetic locus.
- **G3 (holonomy dichotomy) = C6, PROVED (§60.2).** *"The diagonal is holonomic ⟺ `corank(Λ)<∞`."* This is **G3
  verbatim** ("holonomic ⟺ corank(Λ)<∞ ⟺ flat connection"), proved both directions, all bases, via the
  Galois-dimension argument (`dim⟨g⟩-closure = corank(Λ)`). **G3 is essentially DONE.** The sharp invariant is
  `corank(Λ)`, not support cardinality. (Difference-category, per §61.3.)
- **G4 (multi-q Picard–Vessiot correspondence) = §43.1 + §47 + §55, LARGELY DONE.** §43.1: the infinite-base Galois
  correspondence PROVED (Tannakian for affine group schemes + finite-S import; the one new ingredient =
  finite-support invariants-commute-with-limit, Lemma C). §47: the "several-operator" import *dissolved* to the
  classical `n=1` PV method + the co-extension identity 47.1 (`σ_i(A_j)A_i=σ_j(A_i)A_j`, ledger-formalized in
  `FlatConnection.lean`). §55: **inverse-Galois problem CLOSED** — `R_multi = {G : π_0(G) finite abelian}`. So G4
  (the autonomy / C7-charter gatekeeper) is **structurally achieved** here, modulo classical `n=1` lemmas.
- **G5 (unitarity) — strongest seeds (see SEED-E/F/G below).** §22.3: "RH meaningful ⟺ **pure + polarized**" (purity =
  one Lyapunov exponent; polarization = σ-self-duality = the FE) — *defines the RH-bearing objects intrinsically.*

**Implication for the charter (`00-charter`, `00-manifest`).** The verdict "NATIVE proven theorems = 0 / FAILS C5" is
**too pessimistic if these difference-category theorems pass Door-2.** C6 (§60, corank dichotomy) and the
difference-Hölder (§59) genuinely *essentially use* the multi-q apparatus (the infinite-base s-monodromy closure) —
they are candidate C5 (irreducibility) witnesses. **Action flagged:** re-test §59/§60 against Door-2 ("strip the
multi-q vocabulary — does a parent prove it?"). If they survive, the field has its first NATIVE theorems and the
proto-branch verdict upgrades. *Caveat: many other "PROVED HERE" theorems (inverse-Galois §55, λ-subring §56) lean on
classical imports (Etingof, classical IGP, Deligne) and likely FAIL Door-2 — they are IMPORT-reframed. The two genuine
candidates are the corank dichotomy (§60) and the difference-Hölder (§59).*

### SUPPORT — G2 proof program (the most actionable)
- **§34.2 infinite-base ABP criterion = the precise ℚ-form of G2.** Splits into (A) existence of an **archimedean
  trivialization ψ** of the diagonal τ-shift system, finite order; (B) the linear-independence criterion. **(B) is
  plausibly FREE** (unique factorization / ℚ-independence of `{log p}`, ledger-proven); **the entire ℚ-content is (A).**
- **§37 CONSTRUCTS (A): `ψ(s)=∏_{k≥0}ζ(s+k)`** — assembled from local q-Pochhammers, solves `ψ(s)=ζ(s)ψ(s+1)`,
  infinite-order (Hölder-compatible), zeros = ζ-zeros + integer shifts, numerically verified (`psi_infinite_product`,
  dps 25). **§37.5: its ABP regularity = "1/ζ has poles only on Re=½" = RH** (no bypass — difficulty conserved). The
  scalar ψ is rank-1/abelian; the genuine open direction = the **higher-rank / ξ-level completed trivialization** with
  the archimedean seam. *This is a concrete, classical-flavored (Kurokawa absolute-zeta, §40) target.*
- **§33.3 the ℚ-obstruction named:** F_q(t) has a *single* Frobenius ⟹ finite difference eqn ⟹ Papanikolas runs; ℚ has
  *infinitely many* σ_p + Hölder ⟹ no finite eqn ⟹ must go infinite-order. **The F₁/missing-Frobenius wall = the G2 ℚ-gap.**

### SEED — new conjecture candidates (high native smell)
- **(SEED-D, Galois↔ergodic dictionary / difference Morales–Ramis) §11–13.** *Abelian difference-Galois group ⟺
  pure-point / integrable (Kronecker) boundary dynamics; non-abelian ⟺ positive-entropy / chaotic.* The abelian half is
  PROVED (§11, Kronecker spectral theory); the non-abelian half (difference Morales–Ramis) is the open signature
  conjecture, with **Avila's one-frequency cocycle theory as the proved rank-2 case (§12).** Keystone (§13): the
  *same* group G governs both transcendence (orbit of δ) and dynamics (hull) — refined hull-vs-orbit (§14). **TIME
  (A2): the boundary flow IS the system's dynamics/"time"; "non-holonomic time" = a positive-entropy boundary
  cocycle.** Candidate native conjecture **G6 (dynamical localization):** the RH-localization axis is the *reducibility
  / unitarity* of the boundary cocycle (Avila: L=0 ⟺ reducible/a.c.; the σ-self-dual cocycle's spectrum is the zeros) —
  this is the bridge from the time-core (A2) to RH (A1), in Avila-cocycle language. *Smell: native, and the most
  concrete realization of candidate G5 — "unitary holonomy" = "L=0 reducible cocycle".*
- **(SEED-E, Lee–Yang forced-RH family) §81–82, STRONG.** Over Beurling generalized primes (§79), a system whose
  FE-crystalline measure is **Kurasov–Sarnak / Lee–Yang (real-rooted)** type has its zeta's "RH-analogue" **forced by
  construction** (real-rootedness ⟹ real spectrum ⟹, via the Beurling–Weil explicit formula §82, real zeros). **The
  arithmetic ζ is the Poisson/lattice degenerate point (§81.3)** where the Lee–Yang forcing mechanism fails — a
  *structural reason RH is hard.* Candidate native conjecture **G7 (Lee–Yang localization):** "RH = the arithmetic
  (Poisson) base lies on the boundary of the Lee–Yang-crystalline locus where real-rootedness is *marginal*, not
  forced." Connects RH to **Weil's positivity criterion = the missing real-rootedness input** (§82.3). *Smell: native
  (Beurling extension of N1), genuinely non-circular (a sibling family, not an RH-restatement, per §42's anti-trap), and
  it isolates the localization axis (A1) the gatekeepers G1–G4 don't reach.*
- **(SEED-F, FE-rigidity = crystalline-measure rigidity) §80.** FE ⟺ theta-modularity ⟺ Poisson/Fourier self-duality of
  the generalized-integer measure ⟺ **crystalline measure** ⟺ (by Lev–Olevskii/Kurasov–Sarnak/Meyer) **arithmetic
  origin.** Ties the FE to the field's de Branges / Hermite–Biehler / inertia carrier layer. Candidate **G8 (FE =
  crystalline self-duality):** "a difference system admits the σ-base-symmetry FE ⟺ its measure is a Fourier
  quasicrystal." *Smell: native, gives the FE an intrinsic (non-analytic) characterization — relevant to G5's
  polarization/self-duality.*
- **(SEED-G, archimedean = polynomial-multiplier prime) §64, TIME-relevant.** The Γ-recurrence `Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)`
  makes the archimedean place a difference module with the **unique non-constant polynomial multiplier** `(s/2)/π` (all
  finite places have constant multipliers). The diagonal shift `s↦s+1` has **two readings**: finite (`∏_p σ_p`) and
  archimedean (`σ_∞`). **§64.3 (CONJECTURE): the FE `s↦1-s` is the base-swap involution `0↔∞` exchanging the two
  readings**, root number = its automorphy factor (grounded §65–69 via Tate factorization, PROVED for GL_1 and
  monomial GL_n). **§64.4: TWO independent sources of hypertranscendence** — the archimedean Γ-place *and* the infinite
  finite corank. *Smell: native, and the FE-as-place-swap is a clean TIME statement (the involution that makes the
  symmetry possible needs the place at infinity). Directly relevant to candidate G5 (the σ-fixed locus) and A2.*
- **(SEED-H, dynamical period theory) §25–26.** Periods = **Lyapunov exponents (real) + rotation numbers (imaginary) +
  transcendental values (mixed)**; "dynamical Grothendieck period conjecture" `trdeg(periods)=dim G_M`; de Rham↔Betti =
  transcendence↔dynamics comparison (§26). PROVEN cases: gap-labelling (§25.4, rotation numbers ∈ ℤ+ℤα), Chudnovsky
  (CM Γ-values, §27), Papanikolas (F_q(t), §33). *Smell: native sibling to G2; ties the transcendence axis to dynamics
  (A2).* §30: Newton≥Hodge polygon = Mazur's inequality (Lyapunov dominates de Rham).
- **(SEED-I, native ζ_M and intrinsic RH-bearing objects) §22.** Every module has `ζ_M(s)=∏_p det(1-A_p p^{-s})^{-1}`;
  poles = trivial-G_M-rep multiplicity (§22.1); FE ⟺ polarization/self-duality (§22.2); **RH meaningful-and-clean ⟺
  pure + polarized (§22.3).** Candidate **G9 (intrinsic RH locus):** "RH is a property *only* of the pure-polarized
  sub-locus = the arithmetic motives; most of the field has no RH." *Smell: native, defines what RH is *about* — the
  positivity framing never makes this explicit.*

### Native infrastructure worth noting (for proving the gatekeepers)
- **§16 integrability/curvature `F_{pq}=A_q^{-1}σ_q(A_p)^{-1}A_pσ_p(A_q)=1`** = flatness on the prime lattice; PV
  existence for non-decomposable modules PROVED via filtered limit. (Ledger: `FlatConnection.lean`.)
- **§20 difference cohomology `H^*_σ(M)=H^*(ℤ^{(P)},M)`** (group cohomology of the prime lattice), Koszul/exterior
  structure; integrability = vanishing of an H² curvature class. §32: rank-1 acyclicity dichotomy (`H^*=H^*(𝕋^∞)` if
  trivial, else 0). §39: inverse-limit (not colimit), lim¹=0.
- **§38 moduli space** `Mod_d` = twisted character variety of the prime lattice; tangent = H¹_σ; Goldman symplectic
  form; isomonodromy = q-Painlevé/q-Garnier. §57: arithmetic locus = infinite codimension (C5 PROVED).

### Honest caveats (the document's own discipline — important for grading)
- **§42 self-correction #12 (systemic):** "any two RH-equivalent statements are trivially equivalent" — the
  multi-route "convergence" rhetoric is content-free *qua* logical equivalence; genuine content = each route's
  *specific explicit structure* + *actual identities* between pairs. **Apply this when grading SEEDs: a SEED that is
  merely RH-equivalent is worthless; a SEED giving a new explicit object or a non-trivial identity is real.** SEED-E
  (Lee-Yang sibling family) and SEED-D (Avila cocycle) pass; pure RH-restatements fail.
- §61–63: three adversarial audit passes; 18 self-corrections. The genuinely native, Door-2-surviving candidates are
  narrow: **§59 difference-Hölder and §60 corank dichotomy.** Most "structural completeness" (inverse-Galois §55,
  λ-subring §56, adelic local theory §64–69) is import-reframed (Etingof, Deligne, Tate, Bushnell–Henniart, RSZ) and
  likely IMPORT under Door-2.

## [#69] hypertranscendental_galois_field_foundations.md  — Critic's foundations

**Grade:** EXTRACTION-PENDING (founding). High yield, distinctive from #68: this is where the **height-vacuum
diagnosis** and the **secular-coordinate resolution** of G2 live, plus the **two-faces-one-carrier** unification.

### SUPPORT — G2 (multi-q Siegel–Shidlovsky): the deepest structural analysis in the corpus
- **§17 three-pillar S–S architecture + the REAL obstruction.** Classical Siegel–Shidlovsky = Pillar 1 (Siegel's
  lemma / auxiliary) + Pillar 2 (zero/multiplicity estimate) + **Pillar 3 (Liouville/height lower bound)**. The field
  supplies Pillars 1–2 **free** (multiplicative independence of `{log p}`, unconditional). **§17.3 Meta-theorem (the
  height vacuum):** *no transcendence engine can run directly on `{γ_n}` because the zeros carry no arithmetic height*
  — no number field, no house, no Weil height. **This is the actual 165-year wall: not positivity, not circularity, a
  HEIGHT VACUUM.** This is the single most important diagnostic for why G2 is hard.
- **§17.4 the resolution (the field's one non-trivial structural move):** change coordinates from the heightless `γ_n`
  to the **secular constants `P_k = Σ_ρ ρ^{-k}`** (Voros superzeta values) — *the same spectral information*
  (Hadamard-equivalent) but **heighted** (explicit periods in `γ_E, log 2π, ζ-values, Stieltjes constants`). Lands G2
  in **Nesterenko / period-theory / motivic-Galois** territory (§17.5) — a domain *with* transcendence tools, instead
  of the heightless void. **Lever for G2: prove algebraic independence of the Voros `{P_k}` via Nesterenko's method,
  with `G_L`'s multiplicative-independence as the multiplicity input.** *Air: secular forms recalled from Voros 2010,
  flagged for re-derivation.*
- **§19 the explicit secular formula (derived by hand):** `P_1 = 1 + γ_E/2 − ½log4π` (matches Davenport ✓);
  `P_k = 1 − (−1)^k ζ(k)/2^k − a_{k-1}`, `a_j := [s^j](ζ'/ζ)(s)`. **Consequence: `ℚ({P_k}) ⊇ {odd zeta values
  ζ(3),ζ(5),…}`** (the Γ-factor injects `ζ(k)/2^k` into each moment). So **G2 (alg. independence of `{P_k}`) literally
  entails alg. independence of the odd zeta values** = the Ball–Rivoal/Zudilin/Apéry frontier (where theorems and
  methods already exist). *This is the concrete landing of "difficulty conserved but onto a board where we own
  pieces."* Numeric pre-cert flagged: confirm `P_2 = 1 − π²/24 − a_1` vs `Σ_ρ ρ^{-2}`.
- **§11–12 the proof METHOD for G2 (corrects the fiber-functor approach).** §11 (proven negative): the de Branges
  (zero-aware) fiber functor maps `⊗ ↦ ⊕` (de Branges product theorem `H(E₁E₂)=H(E₁)⊕E₁H(E₂)`) — it is **not**
  Tannakian; the obstruction = the additive↔multiplicative seam `[𝔾_a,𝔾_m]`. §12 (the fix, from Mahler rung 2): don't
  make the fiber functor carry the zeros — Mahler's architecture is **(Tannakian ⊗-category) + (separate multiplicity
  estimate)**. So **the G2 engine = a multiplicity (zero) estimate on `G_L`** (Philippon-analog), not a paradoxical
  functor. §14: the correct multiplicity estimate = **subtorus avoidance = LI = PSLQ** (`{F(γ_n)}` avoids proper
  subtori ⟺ no ℚ-resonance among `{γ_n, log N_m}`). §15: the ℵ₀-uniform mechanism = **equidistribution discrepancy
  `D_K < N^{-2}`**. §16: by Landau, `D_K` *is* the explicit-formula prime sum `ΣΛ(x)/√x` — difficulty conserved.

### SEED — new conjecture candidates
- **(SEED-J, two-faces-one-carrier / Li-cone vs genericity) §18, §20 — STRONG, unifies A1 & A2.** Both gatekeeper
  axes are conditions on **one** integer-equivalent coordinate lattice `{P_k} ≅_ℤ {λ_n}` (Li coefficients,
  `λ_n = Σ_j C(n,j)(−1)^{j+1}P_j`, triangular-unipotent over ℤ):
  - **Face A (RH/G5) = a CONVEX-CONE condition:** `λ_n ≥ 0 ∀n` (Li's criterion, RH ⟺ this).
  - **Face B (DSS/G2) = a GENERICITY condition:** `{P_k}` algebraically independent.
  **Object-X = the single point `(Σ_ρ ρ^{-k})_{k≥1}` in moment space; RH = it lies in the Li-cone, DSS = it is
  generic.** The explicit formula computes the point's coordinates (§19). *This is the cleanest statement that A1 (RH
  byproduct) and A2 (transcendence/time) are TWO QUESTIONS ABOUT ONE OBJECT — directly serves the user's "unify the
  two assumptions" goal.* Candidate native conjecture **G10 (cone∩generic):** "the secular point lies in the interior
  of the Li-cone AND is transcendentally generic" — A1∧A2 as one geometric statement on `{P_k}`.
- **(SEED-K, FE-centered Hankel = existing Lean ledger) §22 — connects G5 to formalized math.** Re-center at `s=½`:
  the FE makes `log ξ(½+u)` even, so **the odd centered moments vanish (`τ_{2m+1}=0`) for self-dual / dual-paired
  objects** (parity gift, free). Object-X = the even sequence `s_m = Σ_{γ>0} γ^{-2m}` (prime-computable via the
  explicit formula). **RH (Face A) = Stieltjes–Hankel positivity of `{s_m}` — and this is ALREADY FORMALIZED** in the
  team's moment-positivity repo (dyson's `HermiteHankelDetector`, `scForm_sigNeg_eq_inside`, `κ₋ = n − sig(H)`,
  finite-RH ⟺ trace-Hankel `H ≻ 0`). *Smell: native, and it means candidate G5's positivity face has an existing Lean
  toolchain — a concrete proving ground.* The FE-parity skeleton is the native realization of "the σ-fixed locus."
- **(SEED-L, coordinate-selects-arithmetic) §23.** The expansion center is a *dial* on which arithmetic the moments
  expose: integer center → `ζ(k)` (mixed Tate, Brown's Galois group, tooled); **critical center ½ → `ζ^{(j)}(½)`
  (central values, NON-motivic, no period interpretation, irrationality open).** The FE-natural center (where Face A
  is cleanest, §22) pushes Face B's transcendence onto the *deepest* layer. Candidate **G11 (central-value depth):**
  "the field's irreducible transcendence object is `{ζ^{(j)}(½)}` (Beilinson/central-L-value territory)." *Smell:
  native, locates the true frontier one layer below odd-ζ.*
- **(SEED-M, Tate/prime weld) §21.** `P_k = [motivic ζ(k) part, imported MT(ℤ)] + [prime/Stieltjes `a_j` part, NO
  motivic home]`. The field's *genuinely new* transcendence is the `a_j` (Stieltjes constants `γ_n` + nontrivial
  zeros) and **its rigid coupling to the Tate part inside one period `P_k`.** Candidate **G12 (Tate–prime rigidity):**
  "the secular moment rigidly welds a known motivic block to an unknown prime block — that weld is the new object no
  existing transcendence theory addresses."
- **(SEED-N, family-DSS = GSH) §24 — the field's natural endpoint.** Across primitive `L(s,χ)` the difference bases
  are **SHARED** (same primes `p`, only the twist `χ(p)` differs), so **family-independence is NOT free** — a
  genuinely new obstruction (cross-resonance over common primes, unkillable by unique factorization). The **Grand
  Simplicity Hypothesis (Rudnick–Sarnak)** = the *linear shadow* of family-DSS. Candidate **G13 (family-DSS):** "the
  twisted difference module of the family `{L(s,χ)}` has no cross-resonances ⟺ the character twists alone decouple
  the shared-prime spectra." Places GSH, n-level correlations (Montgomery–Rudnick–Sarnak), pair correlation inside
  one transcendence framework. *Smell: native (genuine extension of N1 to twisted shared-base systems), and the
  shared-base obstruction is structurally new.*

### Cross-reference / overlap with #68
- The DSS conjecture (§3) = G2 = #68's C3. The Euler-product firewall (§9, `EulerProduct.lean`) = #68's §13/§7.
  The Künneth/seam material (§11) overlaps #68's §31 (root number = spectral flow). The distinctive #69 content is the
  **secular-coordinate program (§17–24)** — the height-vacuum→Voros-periods→odd-ζ→Li-cone→central-value chain — which
  #68 does not develop. **These two founding docs are complementary: #68 = the Galois/structural city (proves G1/G3/G4
  in the difference category); #69 = the transcendence/period analysis (locates G2's wall and its moveable lever, and
  unifies A1/A2 on the secular carrier).**

## [#70] hypertranscendental_galois_program.md  — the programme charte

**Grade:** CONJECTURE/META (the wide map). Mostly stubs (B1–B36) + meta-organization, much already captured via
#67–69. Distinctive *new* content = three organizing seeds and a handful of native branch-stubs.

### SEED — organizing/identity seeds (high native smell, serve A1/A2 unification)
- **(SEED-O, the 2×2 corner = the field's identity) Part VIII.** The square `{algebraic/holonomic vs
  hypertranscendental} × {values vs spectra}` has THREE developed corners (motivic periods + Grothendieck;
  Frobenius/Langlands; classical transcendence Siegel–Shidlovsky/Nesterenko) and **one nearly-empty corner: the
  transcendence theory of *spectra* of no-ODE objects** — where the Riemann zeros live. *This is the cleanest
  one-line statement of WHY the branch must exist* (sharper than the vision doc's): the field is the **structural
  completion of the 2×2 square**, with `G_L` (infinite-base difference Galois) as its native Galois group, and the
  explicit formula as the conjectural `primes↔zeros` comparison isomorphism (the analog of Betti↔de Rham). *Directly
  usable in `00-foundations §0` as the self-definition.*
- **(SEED-P, the Two-Faces Law as a universal template) Parts I, VII.** Every spectrum `Σ` admitted to the
  Euler-product/difference frame carries ONE carrier `s_m(Σ)=Σ_{λ}λ^{-2m}` and TWO faces: **Face A** (positivity =
  signed/support-correct Hankel) and **Face B** (transcendence = algebraic independence), with the FE as a parity
  skeleton. The instantiation grid (Part VII) shows **Face A and Face B are orthogonal difficulty axes**: ζ/L =
  A-hard∧B-hard (the apex); Selberg = A-gap-dependent∧B-hard; Ihara graph ζ = B-collapses (algebraic spectrum);
  function field = A-theorem(Weil)∧B-algebraic. *This is the precise structural statement of the user's A1/A2: Face A
  ≈ RH-localization (A1), Face B ≈ transcendence/time (A2), and they are independent axes — which is exactly why the
  gatekeepers G1–G4 (all Face B) don't deliver RH (Face A).* **Candidate G14 (orthogonality theorem):** "Face A and
  Face B are logically independent; RH is the coincidence of both being hard in one spectrum" — a provable transfer
  principle, tractable first on the function-field row.
- **(SEED-Q, Clean/Wall dichotomy) Part XII.** Every branch factors `B = B_clean ⊕ B_wall`, with **all `B_wall`
  equal = the explicit-formula prime↔zero comparison** (Part XI: one uniform bound, four coordinates =
  height/total-positivity/discrepancy/explicit-formula, with two-rate failure signature *margin ~ δ, detection-cost
  ~ log(1/δ)*). *Honest meta-theorem: the field's contribution is the FACTORIZATION (what's free vs the one wall),
  not breaking the wall.* This is the same conservation-of-difficulty the founding docs reach, stated as a clean
  dichotomy. *Relevant to grading SEEDs: a SEED is valuable only if it touches a `B_clean` genuinely or reshapes
  `B_wall`; pure `B_wall` restatements are the §42 trap.*

### SEED — native branch-stubs not already captured (with smell)
- **B7 (Arakelov height of zeros):** supply the missing height (the G2 wall, #69 §17.3) via an Arakelov height on the
  zero-divisor: **places = primes ∪ {∞}, FE = product formula, RH = Bogomolov height-minimality**, equidistribution
  of `{γ log p}` = Bilu small-height shadow. *Smell: native, the direct attack on G2's height-vacuum. (See #89 for
  the dedicated draft.)*
- **B18 (Hilbert–Pólya transcendence obstruction):** a self-adjoint `H` with spectrum `{γ_n}` "cannot be too
  algebraic" — naive constructions fail *because* they'd force `{γ_n}` algebraic, contradicting DSS. *Smell: ties G5
  (the operator) to G2 (transcendence) — the two faces fight; relevant to why candidate G5's operator is hard.*
- **B11 (transcendence ⟹ GUE):** family-DSS ⟹ random-matrix universality (reverses "statistics suggest structure").
  *Smell: native, couples A2 to spectral statistics.*
- **B23 (transcendence tower) / B24 (absolute spectral Galois group) / B26 (transcendence creates the spectrum):** the
  wild category-error mines — the superzeta `𝒵(w)=Σ_ρ ρ^{-w}` is itself hypertranscendental (recurse: ζ→𝒵→𝒵₂→…);
  a profinite `𝔊` acts on `{γ_n}` (zeros as a dessin of the primes); transcendental genericity *forces* a sequence to
  be a zero-set (primes downstream of transcendence). *Smell: deliberately low-prior; B24 (a Galois action on the
  zeros) is the most striking — RH = a fixed-locus of complex conjugation in `𝔊`. Worth a falsification probe.*
- **B32 (edge-value transcendence = Baker, the SOLVED value-corner):** the edge `s=1` values (`L(1,χ)`, class
  numbers, regulators) are Baker-tractable — the value-side solved corner mirroring the function-field zero-side
  solved corner. *Smell: SUPPORT for G2 — Baker's theorem IS the edge's `G_L`-period theorem; unify edge `s=1`
  (Baker) and central `s=½` (open, #69 §23) as two specializations of one period structure.*
- **B27/B13 (dBN constant = transcendence clock):** `Λ` = the flow-time at which Face A (positivity) becomes marginal
  while Face B (transcendence) is invariant; `Λ≥0` (Rodgers–Tao) = the spectrum sits at the transcendence-critical
  edge. *TIME (A2): the de Bruijn–Newman flow as a literal "transcendence clock." Relevant to the dbn entropy thread.*

### SUPPORT / ledger note
- **Part IX §213:** the **Li/secular triangular identity (`{P_k}↔{λ_n}` ℤ-equivalence, #69 §20) is LEDGER-PROVEN** in
  `SecularMoments.lean` (in the axiom audit) — "the first charter result to cross from SEARCH into the LEDGER."
  *Concrete: candidate G10/SEED-J has an existing Lean foothold.*
- Branch↔district map (Part IX) routes every Bi to its companion draft — useful index for the remaining mining
  (B28→moduli-prime-systems #84, B29→spectral-torelli #75, B30→spectral-functoriality #79, B32→edge-value-baker #93,
  B7→arakelov-height #89, B8→geometric-rosetta #88, B15/B20→automorphic #86, B10→dss-multiplicity #72).


## [#71] transcendence-theory-nonholonomic-functions.md  — District D4, the G2 continent

**Grade:** CONJECTURE (native aim) — the dedicated infinite-base Siegel–Shidlovsky (G2) source. **Most actionable
G2 proof-program in the corpus.**

### SUPPORT — G2 (the proof factored into 4 explicit pieces, 3 of them supplied)
- **§3 T-up PROVED (the easy half / upper bound):** `trdeg_F F(diagonal values) ≤ dim G_M`, in the infinite-base
  setting, by specialization (a ring homomorphism kills the relation ideal). *Tier-A formalizable (flagged §7).*
  This is **half of G2, proved.**
- **§4 the lower bound `trdeg ≥ dim(G_M·δ)` factors into THREE named obstructions:**
  - **A (Siegel's lemma in ∞ variables)** — *now SUPPLIED (§8):* the diagonal pullback of an auxiliary form is a
    **Dirichlet polynomial over S-smooth (friable) numbers** `F(s)=Σ_m λ_m n_m^{-s}`, `n_m=∏p^{m_p}` (Prop 8.1,
    ledger-backed `boundedExponentVectorEquivSmooth`, `diagonalAuxiliaryForm_eq_dirichletPolynomial`); the weighted
    Siegel's lemma = **Bombieri–Vaaler 1983** on it, with explicit height (Prop 8.2). *The "∞ variables" was never
    the problem (finite-support §16); the content is the height's dependence on the prime budget `log rad_S=Σ_{p∈S}
    log p`.* **New bridge: transcendence auxiliary functions = smooth-number Dirichlet polynomials** (Granville–
    Soundararajan "pretentious" territory).
  - **B (multi-q Shidlovsky zero estimate, `G_M`-driven)** — *finite-S PROVED (Lemma 5)* by reduction to
    multivariate Mahler (Adamczewski–Faverjon) with rank `dim G_S`; the open part is **Conjecture 5′ (uniformity in
    S)** = "where infinitely many operators stops being free." **Flatness `F_pq=1` is load-bearing:** it makes the
    σ-multi-order a well-posed `ℤ^{(P)}`-action so a single bound `C(N)` can exist.
  - **C (arithmetic of the L-values)** — *the irreducible residue*: the values `n_m^{-s_0}` are ζ-values/zero
    ordinates, not known algebraic/controlled. **Same wall as `ζ(5)`-open, now isolated as a single arithmetic
    obstruction over a built Galois scaffold.** = `spec(H_L)=Spec(L)` keystone = the F₁ arithmetic.
- **§8.3 Prop 8.3 (the race):** G2's lower bound = "vanishing order `T` beats the explicit height+size budget
  against the arithmetic lower bound on `|F^{(T)}(s_0)|`." A,B explicit; **C is the only ungoverned term.** *This is
  the cleanest statement of exactly what must be proven for G2.*
- **§6 Prop 6 (orbit-not-group, PROVED):** `trdeg ≤ dim(G_M·[δ]) ≤ dim G_M`, strict at non-generic δ. **ζ = the
  most non-generic diagonal** (all `q_p=1/p` tied to one `s`) ⟹ small orbit ⟹ hard. *Structural explanation of why
  ζ-values are hard: non-genericity of the arithmetic diagonal (= obstruction C's analytic shadow).* Tier-A
  formalizable (algebraic-group dimension).

### Citation map for G2 (the ladder, §2)
Level 0 differential = Siegel–Shidlovsky / **André–Beukers** Galois form (Beukers, Ann. Math. 2006); Level 1 Mahler
= **Adamczewski–Faverjon** (complete Galois form ~2017–2020), Philippon, Nishioka; Level 1′ q-difference = van der
Put–Singer / Sauloy / di Vizio–Hardouin / Roques; Level 2 multivariate Mahler = Adamczewski–Faverjon; **Level 3
(infinite-base) = OPEN = G2.** *Useful verified-citation anchor for the G2 attempt.*

### SEED
- **(reinforces SEED-C, smooth-number route)** The native auxiliary-function space of the field = **friable
  Dirichlet polynomials** `Σ_m λ_m n_m^{-s}`, `n_m` S-smooth. This is not a side idea — it IS the infinite-base
  Siegel–Shidlovsky method's auxiliary space. Candidate native object N5: "the friable Dirichlet polynomial as the
  field's auxiliary function," with the transcendence race (Prop 8.3) as its native theorem-shape.

### Overlap / null
- §6 hull/orbit = #68 §14; the height residue (obstruction C) = #69 §17.3 height-vacuum; the keystone
  `spec(H_L)=Spec(L)` = #68 §19. The *new* content vs #68/#69 is the **granular 4-piece factorization of G2's
  proof** (§4) and the **Bombieri–Vaaler supply of obstruction A** (§8) — the most concrete G2 attack steps in the
  corpus. No proved native theorem beyond T-up/Lemma-5/Prop-6 (all Tier-A formalizable, flagged).

## [#72] dss-multiplicity-estimate-spectral-genericity.md  — the DSS engine

**Grade:** CONJECTURE-scaffold / BRIDGE (G2 engine). Sharpens #69/#71 with rigorous proofs, numerics, and the
**most concrete G2 landing in the corpus.**

### SUPPORT — G2 (concrete, proved/numeric pieces)
- **§1 multiplicity backbone (PROVED, classical-applied):** Dirichlet-polynomial zero count `N_D(T)=(T/2π)log L +
  O(L)` (Pólya/Langer/Titchmarsh); **Cor 3 complexity law:** absorbing the zeros to height `T` forces length
  `L ≳ T/2πe → ∞` — *no finite Dirichlet polynomial vanishes at every ζ-zero* (the orbit `{F(γ_n)}` is in no
  fixed-length character subvariety). **§1a honesty:** this zero-count is arithmetic-blind (necessary, not
  sufficient) — the arithmetic enters only via §4.
- **§2 Turán/nonharmonic-Fourier face (reduction):** the multiplicity estimate ⟺ a lower bound on
  `|det(n^{-iγ_j})|` (least singular value of the nonharmonic-Fourier matrix `V`). Imports **Ingham (1936) / Turán
  power-sum method / Beurling density**. The real difficulty = sample-point separation (ζ-zero gaps `~2π/log T`) vs
  bandwidth `log L`. Ledger: `multiplicity_det_criterion` (`MultiplicityEstimate.lean`),
  `matrix_nontrivial_kernel_iff_det_eq_zero` (`DSSDeterminant.lean`).
- **§3–4 the Liouville substitute (the KEY new mechanism for G2):** classical transcendence needs ingredient 3
  (Liouville: nonzero algebraic number ≥ H^{-c}) — *absent* for the transcendental spectrum (no algebraicity). The
  **substitute = Weil explicit formula × ℚ-LI of `{log p}`**: a zero-side resonance (a relation among `γ_n`) pushes
  through Guinand–Weil to a prime-side resonance, but the prime side is `ℚ`-non-resonant + integer-rigid
  (`linearIndependent_log_primes`, Lean) ⟹ no low-complexity resonance. **"Where classical transcendence forbids a
  nonzero algebraic number from being small, the field forbids a nonzero prime-side functional from being
  resonant."** *This is the native Liouville analog — the heart of any G2 proof.*
- **§6 obstruction + refined target (important correction):** the explicit formula is **symmetric in the zeros**
  (`Σ_ρ f(γ_ρ)`) — it never sees a *linear combination* `Σa_jγ_j`, so the naive substitute fails. **Fix (T-DSS-2):
  route through the carrier `m_ξ = −Ξ′/Ξ`, whose POLES are the zeros one at a time.** The Liouville substitute =
  rigidity of `{Λ(n)} ↦ {poles of m_ξ}`: a nonzero integer relation `Σa_nγ_n=0` would force an accidental pole
  coincidence in a function pinned by integer-rigid, `ℚ`-non-resonant prime data. *Connects G2 to the Weyl-function
  / canonical-system reconstruction = candidate G5's carrier — A1/A2 meet here.*

### SUPPORT — G2's concrete arithmetic landing (the sharpest in the corpus)
- **§8a RIGOROUS P_k formula (derived in general, not just `P_1`):** `P_k = 1 − (−1)^k ζ(k)/2^k − a_{k-1}`,
  `a_j=[s^j](ζ'/ζ)(0)`, `a_0=log(2π)`. **§8b numerically confirmed** (dps=40, N=2000): matches to 10⁻¹¹–10⁻¹⁸ for
  k≥3. **§8e Lean weld (axiom-clean, Tier A):** `li_secular_pointwise` + `secular_li_pointwise_inv` — the Li↔secular
  ℤ-triangular change of basis is ledger-proven in BOTH directions.
- **§11 the prime block `{a_j}` IS the Stieltjes constants (PSLQ + verified dps=80, residuals ~2e-81):**
  `a_1=ζ(2)/2−γ_E²−2γ_1`, `a_2=ζ(3)−γ_E³−3γ_Eγ_1−(3/2)γ_2`. So `P_2=1−π²/8+γ_E²+2γ_1`, etc.
- **§10–11 the period algebra (the field's DSS, fully concrete):**
  **`ℚ({P_k}) = ℚ(π, {ζ(2k+1)}, {Stieltjes γ_n})`.** Hence **G2/DSS = joint algebraic independence of THREE
  recognizable blocks: `{π}` (Lindemann ✓), `{ζ(odd)}` (Apéry–Ball–Rivoal–Zudilin frontier), `{Stieltjes γ_n}`
  (not even `γ_1` known irrational).** *This is the cleanest possible statement of G2's content — it reduces "the
  zeros are algebraically independent" to a concrete joint-independence problem over classical constants. The
  field's irreducibly-new (no-motive) object = the Stieltjes-constant block and its non-conspiracy with odd-ζ.*

### SEED — G5 / two-faces unification (reinforces SEED-J)
- **§9 RH face closed form (PROVED + numeric):** `λ_n = n·P_1 + (1−n) + Z_n − A_n`, with `Z_n = Σ C(n,j)ζ(j)/2^j`
  (archimedean, all-positive) and `A_n = Σ C(n,j)(−1)^{j+1}a_{j-1}` (arithmetic prime-periods). **RH ⟺ the positive
  archimedean ζ-sum `Z_n` dominates the prime-period sum `A_n` for every `n` = "Ω_∞ ≻ Π" in discrete coordinates.**
  *Candidate G5 in fully explicit Object-X coordinates: RH = archimedean-dominates-prime on the secular point.*
- **§9c the one-point unification (serves the user's A1/A2 goal):** RH = positivity balance (`Z_n ≻ A_n`) and DSS =
  independence (`{ζ(k)} ⊥ {a_j}`) are **two questions about ONE point `(P_k)` driven by the SAME two-place split**
  `P_k = 1 − (−1)^kζ(k)/2^k − a_{k-1}` (archimedean ζ-values vs arithmetic prime-periods). *Both faces = "the
  archimedean and arithmetic places of `G_L` do not conspire" — A1 (positivity non-conspiracy) and A2
  (independence non-conspiracy) are the same structural statement on the secular carrier.*

### Retraction noted (per the corpus's own discipline)
- §7: the `σ_min` conditioning numeric is **retracted** as DSS evidence (it measures sampling regularity, not
  arithmetic genericity); the correct meter = subtorus avoidance = LI = PSLQ (matches #69 §14).

## [#73] difference-galois-cohomology.md  — Branch B5

**Grade:** BRIDGE (native apparatus, cohomology of the difference module). Compact, high signal-to-noise.

### SUPPORT — G3/G4 (native cohomology) + a candidate NATIVE theorem
- **§2 (PROVED, clean half):** `H^*(G_L,ℚ) = ∧^*(V)`, the **exterior algebra on the prime lattice** `V=⊕_p ℚ·e_p`,
  one degree-1 generator `e_p = "d log p"` per prime; `H^1=V` = the log-prime/Adams lattice. The cohomology of the
  multiplicative (free, zero-blind) wing, fully explicit.
- **§3 the σ-parity = FE-parity weld (PROVED HERE, and LEDGER-PROVEN — candidate NATIVE):** since `σ` acts as
  inversion `θ_p↦−θ_p` (FE = `w↦1/w`), `σ|_{∧^k V} = (−1)^k`, so **`H^even` = FE-surviving / `H^odd` = FE-killed** —
  reproducing foundations §22's `τ_{2m+1}=0` *cohomologically*. **Machine-checked, axiom-clean:**
  `fe_odd_moment_vanish` + `fe_centered_odd_moment_vanish` (`FunctionalEquationParity.lean`, the moment level) and
  `exteriorPower_map_neg_id` (`∧ⁿ(−id)=(−1)ⁿ·id`, `ExteriorParity.lean`, the genuine exterior-power level). *This is
  a genuine native weld with a Lean foothold — worth re-testing against Door-2 as a candidate native theorem (it
  ties the difference-Galois cohomology grading to the FE; a parent discipline would not state it without the
  multi-q/prime-lattice apparatus).*

### SUPPORT — G4 (autonomy / Tannakian gap) and G5 (localization)
- **§4 the monoidality obstruction `ω ∈ H²(G_L)`:** the de Branges `⊗↦⊕` (foundations §11) vs the cup product `∧`
  disagree by a 2-cocycle `ω`; **`ω=0 ⟺ G_L is Tannakian ⟺ a genuine motive exists ⟺ the zero-realization
  succeeds.`** This locates G4's autonomy gap (and G5's zero-realization) as ONE explicit H² class. *Not computed —
  whether `ω=0` is the open core.*

### SEED
- **(SEED-R, ω = Koszul homology in the ∞-prime limit) §6 [SPEC].** Candidate: `ω = the Koszul homology class of the
  prime lattice in the ∏_p limit` — `ω=0 ⟺ the ∞-prime Koszul complex `∧•V ⊗ Sym•V` stays acyclic`. The finite
  Euler shadow = the `e–h` duality `Σ_{i+j=k}(−1)^i e_i h_j = 0` (LEDGER-PROVEN, `EHKoszulDuality.lean`). *A
  homological "fourth language" for the renormalization wall (alongside ξ-outer singular-inner condensation,
  LP-survival, explicit-formula limit) — relevant to A1/G5: RH = "a free/exact finite structure survives the
  infinite prime product."* Candidate **G15 (Koszul-acyclicity):** "RH/Tannakian ⟺ no Koszul homology condenses in
  the renormalized `∏_{p≤P}→∏_p` limit."

### Note
- The exterior/symmetric Koszul duality (`∧•V` cohomology ring ↔ `Sym•V` secular/moment coordinate ring) is a clean
  native structure tying #73 (cohomology) to the secular-moment carrier of #69/#72 — the two wings are Koszul-dual.

## [#74] dss-across-the-period-nonperiod-divide.md  — locating DSS's open core

**Grade:** CONJECTURE/SPECULATION (G2-locating). Refines #72 §11's "DSS = indep of {π,ζ(odd),Stieltjes}".

### SUPPORT — G2 (locates the wall precisely)
- **The claim:** DSS = alg. independence of `{π} ∪ {ζ(3),ζ(5),…} ∪ {γ₁,γ₂,…}` (Stieltjes). The first two are
  **periods of mixed Tate motives `MTM(ℤ)`** (GPC-conditional, motivic Galois group = `𝔾_m ⋉ free-pro-unipotent`
  in odd degrees — Deligne–Goncharov; tooled). The **Stieltjes constants are conjecturally NOT periods** —
  exponential-period-like regularization constants (`γ_E = −∫₀^∞ e^{−x}log x dx`), **outside** the period algebra
  GPC controls.
- **The relocation (the new content): DSS = GPC + (DSS-cross)**, where **(DSS-cross) = `{γₙ}` algebraically
  independent of the entire period algebra of `MTM(ℤ)`** — *a statement ACROSS the period/non-period divide, which
  neither GPC nor the motivic Galois group sees.* **So G2's genuinely-open core is the Stieltjes side, not the
  zeta side.** The right framework = **exponential-motives / Nori motives (Fresán–Jossen)**, whose period
  conjecture would cover it (but is less accessible, Galois group uncomputed).
- **Strategy implication for G2:** aim the Nesterenko multiplicity-estimate's arithmetic lower bound at the **`s=1`
  Laurent data of ζ** (where the `γₙ` live), not the integer special values (where Nesterenko already has purchase
  via `{π,e^π,Γ(1/4)}`). The `a_j=[s^j](ζ'/ζ)(0)` are where the two worlds **mix in one coefficient** (#72 §11), so
  each `P_k` is itself a period/non-period *sum*.

### SEED
- **(SEED-S, regularization creates transcendence) §UPDATE.** Meta-principle: **zeta-regularization /
  Hadamard-finite-part is a transcendence-CREATING operation** — it manufactures constants algebraically
  independent of the input's Kontsevich–Zagier periods. Evidence: `log 2π = −2ζ'(0)`, Glaisher `ζ'(−1)=1/12−log A`
  are exponential-period-like and (numerically) free of the period field. Candidate native conjecture **G16
  (regularization-freshness):** "the regularization constants attached to a hypertranscendental object are
  transcendentally fresh relative to its periods — this freshness is the field's irreducible new transcendence."
  *Smell: native (the no-motive block), and it explains structurally why the field is not a sub-case of period
  theory.*

### Numeric support (PSLQ, dps 150 & 300, maxcoeff 1e12, guard-safe; `computations/dss_cross_divide/`)
- **No low-height relation** among `{1,γ₀,γ₁,γ₂,γ₃}` (Stieltjes ℚ-LI), nor in cross sets `{1,π²,ζ3,ζ5,γ₀,γ₁,γ₂}`
  and degree-2 `{1,γ₀,γ₀²,π²,ζ3,γ₁}`. **Positive control:** the *known* relation `2ζ'(0)+log2π=0` correctly
  detected — so the negatives are meaningful. *Numeric tier, not proof, but strong support for (DSS-cross).*

### NULL / overlap
- The "DSS = indep of {π,ζ(odd),Stieltjes}" reduction = #72 §11. The *new* contribution is the period/non-period
  divide diagnosis (the Stieltjes side is the open core, beyond GPC) and the regularization-freshness meta-principle
  (SEED-S). Finite shadow `spectrum_esymm_algIndep` ledger-proven; the cross-divide apex is open.

## [#75] spectral-torelli-inverse-problem.md  — Branch B29

**Grade:** BRIDGE/CONJECTURE. Carries one genuinely PROVED (and ledger-proven) theorem + a sharp G5-relevant
separation.

### SUPPORT — proved theorem + Lean (Torelli injectivity / secular-moment faithfulness)
- **§1 Spectral Torelli (injectivity), PROVED:** the secular moments `{s_m}_{m≥2}` **determine** the completed
  L-function `ξ` (resolvent `R(z)=Σ_ρ[1/(ρ−z)−1/ρ]` has poles = zeros with residues = multiplicities → Hadamard →
  FE+normalization fix `a,b`). **The secular-moment coordinates are FAITHFUL** — justifies treating `{s_m}` as
  Object-X. **LEDGER MILESTONE:** `powerSum_torelli` FULLY ledger-proven (`PowerSumTorelli.lean`, axiom-clean):
  equal secular power sums ⟹ equal zero multiset, via the from-scratch `MultisetNewton.lean` (psum bridge + Newton's
  identity for multisets, both absent from mathlib) — strong-induction inversion `(p_k)↦(e_k)` + Vieta + roots.
  *Caveat: the finite version is symmetric-function theory ⟹ likely IMPORT under Door-2; the infinite
  resolvent/Hadamard passage is Tier B.*

### SEED / SUPPORT — G5 (the three-cut image separates RH from arithmeticity)
- **§2 the image `Φ({ξ})` = THREE INDEPENDENT cuts on moment space:** **(E)** existence/realizability (order-1,
  FE-symmetric divisor), **(A)** arithmeticity = Euler product (the `EulerProduct.lean` firewall), **(P)** positivity
  = RH (Li/Bogomolov). **RH is ONLY cut (P).** The fakes (Davenport–Heilbronn) live in `(E)∧¬(A)` and **can even
  satisfy Hankel-positivity without being genuine** ⟹ **positivity (P) does NOT imply arithmeticity (A).** *This is
  the no-margin/integrality lesson in inverse-problem form: genuineness is the Euler cut, not the positivity cut —
  any criterion that "sees RH" from positivity alone has confused (P) with (A) and will pass a fake.* **Directly
  sharpens candidate G5:** the unitarity/positivity gatekeeper must be conjoined with the Euler-product cut (A) to
  exclude fakes — G5 alone (positivity) is insufficient.
- **§3 overdetermination = the defining equation of genuineness (reframe → dyson):** each `s_m` is computable two
  ways (zeros `Σ_ρ ρ^{-m}` vs primes via `−ξ'/ξ`); a genuine spectrum is the **overdetermined locus where they
  agree for all `m`** — image is thin (infinite-codimension). Candidate **G17 (overdetermination):** "RH-bearing
  objects = the zero-side=prime-side overdetermined locus ∩ (E)∧(A); the explicit formula is its equation system."
  *Smell: native, ties the inverse problem to the explicit-formula carrier.*

## [#76] carrier-unifies-dss-and-rh-faces.md  — the carrier germ unifies A1 & A2

**Grade:** BRIDGE/CONJECTURE — **the single cleanest statement of the A1/A2 unification the user is after**, with
both finite layers ledger-proven.

### SEED — G5 / the A1↔A2 bridge (STRONGEST unification find, directly serves the user's goal)
- **§0 ONE germ, two readings.** The carrier `m_ξ(z) = −Ξ′/Ξ(z) = Σ_ρ 1/(ρ−z) = Σ_{k≥0} P_{k+1} z^k`. So **the
  secular moments `{P_k}` ARE literally the Taylor coefficients of the carrier at 0.** The two assumptions are two
  coordinate systems on this one analytic germ:
  - **A1 (RH / localization / positivity) = the germ's GLOBAL analytic type:** `m_ξ` Herglotz ⟺ `κ₋=0` ⟺ no
    ℂ⁺-poles ⟺ RH.
  - **A2 (DSS / transcendence / time) = the germ's INFINITE JET at 0:** `{P_k}` algebraically independent.
  *"RH reads the germ's monodromy/positivity type; DSS reads its infinite jet at a point. They are independent
  readings of the SAME function — which is exactly why neither implies the other (the user's finding that A1/A2 are
  on orthogonal axes), and why the field needs both wings."* **Candidate G5 in carrier form: `m_ξ` Herglotz/unitary
  ⟺ RH** — this IS the "unitary holonomy on the σ-fixed locus" gatekeeper, made concrete as the carrier's analytic
  type.
- **The unification's payoff (the deepest possible result the user named):** because both faces live on **one
  germ**, a *single* rigidity statement feeds both — "any quantitative bound forcing the germ to be
  transcendentally generic at 0 (DSS/A2) is, by analytic continuation of the same germ, a constraint on its global
  pole structure (RH/A1)." **The common ingredient = the multiplicity estimate on `G_L`** (Nesterenko jet-
  independence for A2 + inertia-rank input for A1). *This is the candidate mechanism by which the time-core would
  FORCE unitarity — the §4-foundations "make RH and time one statement."*

### SUPPORT — both finite layers LEDGER-PROVEN (axiom-clean)
- **Brick 0 (finite RH/A1 face):** `multiPair_carrier_exact_neg_inertia` — for a finite carrier with `k` off-line
  conjugate pairs, the Pick form has **negative inertia exactly `k`** (`κ₋ = #off-line zeros`), via explicit
  Krein–Langer factorization + Cauchy non-degeneracy. *Unconditional, quantitative: each off-line zero = exactly one
  negative square; RH ⟺ κ₋=0 is the `k=0` limit.*
- **Brick 1 (finite DSS/A2 face):** `spectrum_esymm_algIndep` — elementary-symmetric coords of `n` indeterminate
  spectral points are algebraically independent over ℚ (full trdeg `n`), via mathlib's fundamental theorem of
  symmetric polynomials; ≡ alg. independence of finite power-sum moments by Newton (char 0).
- **Brick 2 (the infinite passage) OPEN:** A1 needs Krein–Langer `N_κ` + Nevanlinna/Pick at infinite nodes
  (mathlib gap, regularized Hadamard); A2 = `{P_k}` jet independence = `{π,ζodd,Stieltjes}` (open math). *The open
  core is "one germ, two readings," both finite layers closed.*

### Numeric
- PSLQ (dps=220, height 1e12, `computations/dss_secular_moments_pslq/`): no spurious low-height ℚ-relation among
  `{P_2,…,P_8}` of the actual ξ-zeros beyond those forced by the ζ-value/Stieltjes formula.

### Verdict for the review
- **This is the doc to mine first for the user's "unify A1 and A2" goal.** It gives the concrete unifying object
  (the carrier germ `m_ξ`), the precise two-readings statement, the candidate single-rigidity mechanism (the
  multiplicity estimate feeding both), and ledger-proven finite anchors on both sides. Candidate G5 should be
  *stated in carrier form*: "RH ⟺ `m_ξ`(= −Ξ′/Ξ) is Herglotz (κ₋=0) on ℂ⁺" — the unitarity gatekeeper as the
  carrier's positivity type, with the jet (DSS/A2) the same germ's transcendence.

## [#77] rh-byproduct-secular-hankel-overdetermination.md  — Face A / secular total positivity

**Grade:** IMPORT (reframed) + a few [PROVED HERE]. The Face-A (RH/A1 positivity) determinantal analysis of the
secular carrier. Heavy classical import (ASW/Edrei, CNV, GORZ, de Bruijn, Rodgers–Tao) but with genuine native
coordinate-realizations.

### SUPPORT — G5 / Face A (RH = uniform secular total positivity)
- **§1–2 the two determinantal faces of RH on the secular data `c_n=ξ(½)e_n({1/γ²})`:** **Hankel face** (Hermite,
  reality of squared-zeros) with `κ₋ = #(negative eigenvalues of H_K) = #(off-line σ-quadruples)` — *realizes the
  field's spectral index `κ₋` as the negative-eigenvalue count of an explicit, prime-computable Hankel matrix*
  (new; `secular_hankel_signature`); **Toeplitz face** (Pólya-frequency / total positivity, negativity of
  squared-zeros). RH ⟺ both.
- **§5–6 RH = uniform (all-order) total positivity = `Λ=0`:** RH ⟺ secular Toeplitz `[c_{i−j}]` totally positive to
  ALL orders ⟺ `Ξ∈Laguerre–Pólya` ⟺ **`Λ≤0`** (de Bruijn–Newman), where `Λ = the TP-onset time of the secular
  form` (new realization). **Rodgers–Tao `Λ≥0` (the FE-forced half)** ⟹ **RH ⟺ Λ=0 = the no-margin.** *Candidate G5
  in Face-A form: RH = `Λ=0` = uniform secular total positivity.*
- **§6 the field weld (SEED for A1/A2):** `Λ≥0` = the **multiplicative/equidistribution side** (free, zero-repulsion
  = diagonal flow equidistributes on `𝕋^∞` by unique factorization); `Λ≤0` = the **archimedean boundary
  positivity** (the frontier wing); `Λ=0` = the seam = the no-margin. *The de Bruijn–Newman axis re-expresses the
  field's free-vs-frontier (A2-free vs A1-hard) split; Rodgers–Tao = the proof of the free half. TIME-relevant: the
  dBN heat flow is the "transcendence clock" (cf. #70 SEED B27).*

### SEED / [PROVED HERE] — the moment≠frequency separation (the no-margin, made exact)
- **§4 Thm 6 (PROVED HERE, witness):** a Stieltjes moment sequence need NOT be Pólya-frequency — witness `a_n=1+4^n`
  has PSD Hankel (Stieltjes) but negative Toeplitz minor `a_1²−a_0a_2=−9`. **So the FREE moment-positivity (Hankel,
  FE-forced) is strictly weaker than the Toeplitz total positivity (= RH).** *Candidate native lemma N6: "moment
  positivity ⇏ frequency positivity" — the precise reason RH isn't a free byproduct of FE-positivity. Reinforces
  #75's (P)≠genuineness lesson.*
- **§4 Thm 7 (PROVED HERE/NUM) the no-margin exact:** an off-line zero at distance `δ` breaks Toeplitz TP, but the
  **first violated minor's order grows as `δ→0`** with **vanishing magnitude** — no fixed-order TP test certifies
  RH. *The two-rate no-margin signature (#70 SEED-Q): margin~δ, detection-cost~order↑.*

### What the FE forces FOR FREE (genuine byproducts, §3)
TP₁ (`c_n>0`, Pólya `Φ>0`); moment/Stieltjes Hankel positivity (free); TP₂/Turán (`c_n²≥c_{n-1}c_{n+1}`,
Csordas–Norfolk–Varga, with scale-free margin monotonically ↓ — the no-margin trend); asymptotic each-order TP_d
(GORZ). *These are real theorems the field's FE-structure delivers; RH is only the UNIFORM completion.*

### NULL / ledger
- Mostly classical determinantal theory reframed (likely IMPORT under Door-2). Only Lean theorem:
  `secularHankel_posSemidef` (finite real points ⟹ PSD Hankel). The genuine native contributions: the `κ₋` =
  Hankel-negative-eigenvalue-count identification, `Λ` = secular-TP-onset-time, and the moment≠frequency witness
  (Thm 6). Overlaps #76 Brick 0 (κ₋ exact) and #72 §9 (Li `Z_n≻A_n` = linear face vs this determinantal face).

## [#78] secular-positivity-hierarchy.md  — the secular-positivity continent

**Grade:** IMPORT (reframed, heavy classical) + several native operator-realizations with Lean footholds.
**SINGLE RICHEST SOURCE FOR CANDIDATE G5** — RH given in ~7 concrete operator/unitarity/Hodge-Riemann forms, all
unified, several validated numerically across 4 L-functions and with pointwise Lean theorems.

### SEED — candidate G5 (unitarity gatekeeper) in many concrete, validated forms
The doc realizes "RH = unitarity/self-adjointness of the secular operator" in successively sharper forms; **state
candidate G5 using these, they are the native home of "unitary holonomy on the σ-fixed locus":**
- **§12 Conjecture F (CMV/OPUC) — THE most direct G5:** via Arakelov `w=1−1/ρ` (ledgered `ArakelovW`: `|w|=1 ⟺
  Re=½`, `w_ρ w_{1−ρ}=1`), **RH ⟺ the secular CMV/OPUC operator is UNITARY ⟺ Verblunsky coefficients `|γ_k|<1`
  ∀k**. Validated (N=40) across **four L-functions** (ζ, Dirichlet β, Ramanujan Δ deg-2, elliptic 11a deg-2): all
  `|γ_k|=0.993–0.999` (no-margin AT the circle); off-line ⟹ `|γ_k|>1` detected robustly. *This IS "unitary
  holonomy" — the secular circle operator's unitarity = RH.*
- **§14 Conjecture G (capstone) — G5 in purest form:** RH ⟺ **`ι = κ`** (the FE-inversion `w↦1/w` equals
  conjugation `w↦w̄` on the spectrum) ⟺ **the secular operator's FE-involution coincides with its adjoint
  (FE-self-duality)** ⟺ unitary/self-adjoint. **Pointwise case LEDGER-PROVEN:** `sigmaConj_fixed_iff_critical`
  (`1−s̄=s ⟺ Re s=½`). *Candidate G5 = "RH = the uniform `ι=κ` = the FE-involution is the adjoint."* Unifies ALL
  faces: orbit-size-2 (Thm 1) = `|w_ρ|` on circle = CMV unitary (§12) = Jacobi self-adjoint (§9) = Hankel/Toeplitz
  PSD/PF (§2–4) = `Λ≤0` (§5).
- **§9 Conjecture D (Jacobi/Hilbert–Pólya):** RH ⟺ the secular Jacobi operator `J` (built source-purely from secular
  moments, eigenvalues `−1/γ²`) is self-adjoint ⟺ `b_k>0` ∀k. `J = −Δ+V` = lattice form of the prime Schrödinger.
- **§27 Berry–Keating/Connes (FE-invariant `u=s(1−s)=¼+γ²`):** RH ⟺ `u_n` real ≥¼ ⟺ a secular operator in `u` is
  positive self-adjoint (`Δ≥¼`). Ledgered pointwise (`BerryKeating.lean`: `berryKeatingU_sigma`,
  `..._critical_param`, `..._re_ge_quarter_on_critical`, `..._nonreal_of_offCritical`). *The cleanest positive-
  spectrum H–P form; ties to Connes' Δ and Berry–Keating H=xp.*

### SEED — the deepest G5/A2 form: RH = Hodge–Riemann positivity of the Weil representation (§19–22) — STRONG
- **§19–22 (the apex, grounded):** RH ⟺ **`Q_W ⪰ 0` ⟺ the Hodge–Riemann bilinear relations for the metaplectic /
  Weil representation of `SL₂(ℝ)`** (the theta-modularity group that produces ξ's FE). The generators are concrete:
  **the dBN heat flow `e^{tu²}` = the unipotent ample/Lefschetz class `X=u²`; the FE involution `σ` = the elliptic
  `S`-element (Fourier).** Together they generate `SL₂(ℝ)` acting by the Weil rep on ξ's spectral realization.
  **The Lefschetz isomorphism `X^k` is FREE (structural, the Weil rep itself); RH = the Hodge–Riemann SIGNATURE
  (the deep half)** — matching function-field hard Lefschetz generator-for-generator (ample↔heat, cup product↔Q_W,
  Hodge–Riemann↔RH). Ledgered: oscillator commutators `[H,X]=2X,[H,Y]=−2Y,[X,Y]=−4H` (`OscillatorAlgebra.lean`).
  **TIME/A2 connection:** the archimedean wing = the Weil representation of `SL₂(ℝ)` (theta-modularity); the heat
  flow (= transcendence/dBN clock) is the unipotent ample class, the FE is the elliptic Fourier element. *Candidate
  G5 in its most geometric form — "RH = the unitarity (Hodge–Riemann signature) of the time-symmetry group `SL₂(ℝ)`
  acting on ξ", which is exactly "the clock preserves a norm."*

### SUPPORT — G3/G4 weld + the free-vs-frontier split (serves A1/A2)
- **§17 Conjecture H (operator ⟷ `G_L`):** the secular operator is a `G_L`-module. **The 𝕋^∞-part (multiplicative
  wing) acts by ISOSPECTRAL integrable flows (Toda §10–11 on the line, Schur/Ablowitz–Ladik §12 on the circle) —
  FREE, RH-BLIND; the secular invariants are its Casimirs (the equidistribution/prime content, A2-free). The
  σ-element acts by the FE involution ι; RH ⟺ σ acts as conjugation κ (the non-isospectral, archimedean direction,
  A1-hard).** *This is the cleanest realization of "A2 (transcendence/time/free flow) vs A1 (RH/localization/the σ
  reality)" on a concrete operator — and it explains WHY every secular invariant is RH-blind (they're Casimirs of
  the free flow).*
- **§11 the isospectral insight (genuine structural finding):** the Toda flow on the secular Jacobi matrix is
  CONFIRMED (`E1`, rel 1e-14) but **isospectral, hence RH-blind**; the dBN flow MOVES the zeros (non-isospectral),
  so it is NOT a Toda flow. *The integrable structure lives entirely in the free direction; RH requires leaving the
  isospectral leaf.* Candidate native lemma: "the secular invariants are Toda Casimirs ⟹ RH-blind by construction."

### SUPPORT — function-field model (Door-5 proving ground for G5)
- **§13, §15:** function-field RH = "the finite Frobenius is unitary," **provable from Poincaré duality + hard
  Lefschetz (Hodge–Riemann)**; number-field RH = "the infinite secular CMV operator is unitary," with the **single
  missing ingredient = the self-dual pairing `Q_W`** (the archimedean-completed cup product) that the archimedean
  place must supply. *Localizes G5's gap to exactly "the duality pairing," present over `F_q`, sought over ℚ = the
  F₁/archimedean cohomology.*

### Ledger footholds (axiom-clean, relevant to G5)
`SigmaOrbit` (critical line = fixed locus of σ∘conj, the pointwise `ι=κ`); `ArakelovW` (`|w|=1⟺Re=½`, FE
inversion); `SecularNewton`/`SecularHankel` (Newton duality, finite Hankel PSD); `BerryKeating` (pointwise `u`);
`OscillatorAlgebra` (the Weil-rep commutators). *Candidate G5's positivity face has a real, growing Lean
toolchain.*

## [#79] spectral-functoriality-operations-calculus.md  — Branch B30

**Grade:** IMPORT (λ-ring / symmetric-function theory, reframed) + extensive Lean ledger. The "clean half" of the
operations branch — Satake-side fully closed, zero-side = the wall.

### SUPPORT — G4 (the master spectral Langlands group) + SEED (operations = correlations)
- **§2 operations = correlation hierarchy (REFRAME → Montgomery/Rudnick–Sarnak):** read through the explicit
  formula, **`⊗` (Rankin–Selberg) = pair correlation R₂ (Montgomery); Sym^k/k-fold = the n-level R_k
  (Rudnick–Sarnak).** "The field's operations calculus IS the statistical correlation hierarchy." *Connects A2
  (transcendence/structure) to GUE universality — reinforces #70 SEED-B11.*
- **§4/§8 the moment λ-ring `𝓜` (G4/B34, the master group):** `𝓜 = ℚ[p_m(π)]` = the **free λ-ring on the Adams
  operations (prime power sums)**; conjecturally the **coordinate ring of the field's master spectral Langlands
  group `π₁(𝒮)`** (G_L-reps ↔ 𝓜-comodules). §3: **functoriality = a λ-ring homomorphism preserving the two faces**
  (GRH and DSS are functorial invariants of the whole λ-ring). *This is the autonomy/Langlands gatekeeper (G4) in
  λ-ring form; the master group is the field's terminal object.*

### SUPPORT — extensively LEDGER-PROVEN (the field's clean Satake-side half, axiom-clean)
- `adamsPowerSum_tensor`: `p_m(π₁⊗π₂)=p_m(π₁)p_m(π₂)` ⟹ self-dual `π⊗π̃` gives `‖p_m‖²` = the nonneg
  pair-correlation weight (makes "operation=correlation" EXACT at ledger grade).
- `adamsPowerSum_isobaricSum` (⊕ adds), `adamsPowerSum_comp` (ψ^m∘ψ^k=ψ^mk, Adams monoid), `adamsPowerSum_one`.
- `chebyshevU_eval_plethysm`: `p_m(Sym^k π)=U_k(p_m/2)` (machine-proved via Chebyshev recurrence, supersedes the
  numeric cert); `localFactor_coeff_esymm` (∧^k face); `eh_koszul_duality` (the e–h / ∧•⊣Sym• Koszul duality, all
  degrees). *The operations λ-ring's three bases (e_k/∧^k, p_k/ψ^k, h_k/Sym^k) + their duality are all in Lean.*

### SEED
- **(SEED-T, the e–h Koszul weld B30↔B5) §9–10:** the reciprocity `E(x)·H(x)=1` (operations λ-ring) IS the
  `∧•⊣Sym•` Koszul duality (B5 cohomology); the FE `(−1)^k` parity is the Koszul sign — *one structure underlying
  both branches.* Reinforces #73 SEED-R (ω = Koszul homology in the ∞-prime limit). Candidate: "the operations
  calculus and the cohomology grading are the same Koszul complex of the prime lattice."

## [#80] superzeta-tower-resolution-B23.md  — Branch B23 self-adjudicated

**Grade:** CONJECTURE (resolved-negative + salvage). A model of the field adjudicating its own wild conjecture by
its own First Theorem.

### SUPPORT — the seam, ledger-proven (Σ additive vs ∏ multiplicative)
- **Verdict (uses the First Theorem):** the superzeta `𝒵(w)=Σ_ρ ρ^{-w}` has **no Euler product** (frequencies
  `{log ρ}` not on a ℚ-LI multiplicative base; `{ρ}` not multiplicatively closed) ⟹ by the First Theorem it is a
  "fake" — the transcendence tower `ζ→𝒵→…` does NOT recurse spectrally. *"Fixed point = the prime" is a
  seam-collapse category error: it asks the zeros (additive side) to acquire prime (multiplicative) structure,
  which the seam `[𝔾_a,𝔾_m]≠0` forbids.*
- **LEDGER WITNESS (`SuperzetaResolvent.lean`, axiom-clean):** `superzeta_eq_sum_resolvent` — the superzeta is the
  **additive resolvent trace** `Σ_i(1−r_iX)^{-1}` (Σ, not ∏), contrast `coeff_localFactor_series` (the
  multiplicative product over a prime base); `superzeta_coeff_eq_powerSum` — its k-th coefficient = `P_k`. *The
  Σ(spectral/additive) vs ∏(prime/multiplicative) split — the seam itself — is now a Lean theorem.* Concrete
  support for the additive↔multiplicative seam structure underlying all the gatekeepers.

### SEED — the motivic period tower (the salvage, expands B23 to a positive program)
- **(SEED-U, B23′ motivic period tower) §3:** the tower DOES recurse, but **motivically, not spectrally**. The
  period algebra `𝒫_𝒵 = ℚ⟨P_k : k≥2⟩` (superzeta values = secular moments) carries a **motivic Galois action**
  (Kontsevich–Zagier / mixed-Tate); *that* action — not a second `G_L` — is the next tower level; the "fixed point"
  = the pro-unipotent radical of the motivic Galois group of `𝒫_𝒵`. **The two towers' non-interaction IS the
  seam:** the multiplicative/spectral tower (difference-Galois) is dead at level 2; the additive/period tower
  (motivic-Galois) is alive. *Smell: falsifiable (Voros's explicit `𝒵(2m)∈{π,ζodd,Stieltjes}`), non-circular
  (reads values not zeros), respects the seam, routes into Nesterenko/motivic-Galois (the G2 height-vacuum target).
  Candidate native conjecture: "the field has TWO Galois towers — a dead spectral one and a live motivic one — and
  the seam is their non-interaction."*

## [#81] seam-is-the-period-nonperiod-divide.md  — one archimedean obstruction behind both faces

**Grade:** CONJECTURE/SYNTHESIS. A strong A1↔A2 unification: both apex faces = the SAME archimedean obstruction.

### SEED — A1/A2 unified at the seam (directly serves the user's "unify the two assumptions")
- **The seam = the period/non-period divide (concrete identification):** the multiplicative wing (Euler product,
  integer ζ-values) supplies **periods** (`{π,ζ(odd)}`, GPC-shaped); the archimedean wing (Γ-factor, pole at `s=1`)
  supplies the **non-periods** (`{γ_n}` Stieltjes, log2π, Glaisher — exponential/regularization constants); the
  **seam = the completion `ξ=(Γ-factor)×ζ`** glues period to non-period. **§1:** each secular moment
  `P_k = ζ(k)[period] − a_{k−1}[non-period]` is *literally* a period+non-period sum glued at the seam.
- **§2–4 the unification (SPECULATION, the new claim): BOTH apex faces are the SAME archimedean obstruction:**
  - **A2/DSS** = "is the non-period jet generic?" (DSS-cross, the Stieltjes side, archimedean).
  - **A1/RH** = "is the archimedean-completed carrier type positive?" (`m_ξ` Herglotz / `κ₋=0`; the off-line poles
    are multiplicative-visible/finite-handled, but the regularization completing the carrier is archimedean).
  - **The unified bet:** the field needs **ONE archimedean rigidity input** feeding both — simultaneously (a) the
    Nesterenko arithmetic lower bound forcing DSS-cross [A2] and (b) the Herglotz/positivity input forcing
    `κ₋(m_ξ)=0` [A1]; the **multiplicity estimate** is the common algebraic ingredient. *Candidate: "RH and
    transcendence are forced by one archimedean rigidity bound on the `s=1`-Laurent/Γ-factor data" — the concrete
    form of "the time-core forces unitarity."*
- **Prediction (falsifiable in spirit, valuable for the program):** apex progress must engage the **Γ-factor /
  `s=1`-Laurent (Stieltjes) data, NOT the integer ζ-values**. Multiplicative-only tools (Euler product, prime sums,
  ζ-values) are **structurally blind** to both apex obstructions (wrong side of the seam) — *this turns the parent
  project's empirical "RH-blindness/circularity of prime-side methods" into a structural theorem.* **Directly
  relevant to grading the whole corpus:** any SEED on the multiplicative/prime side is structurally apex-blind; the
  live SEEDs are archimedean (Stieltjes/Γ-factor/regularization-freshness, cf. SEED-S).

### Proven anchors / cross-ref
- Finite RH face `multiPair_carrier_exact_neg_inertia` (#76 Brick 0) + finite DSS face `spectrum_esymm_algIndep`
  (#76 Brick 1) — both ledger-proven; the infinite apex is the single archimedean obstruction, here named/localized
  (seam = period/non-period divide). Synthesizes #74 (period/non-period), #76 (carrier germ), #69 §11/§21
  (Stieltjes block), SEED-S (regularization-freshness).

## [#82] prime-zero-period-comparison.md  — Branch B9, the period comparison

**Grade:** CONJECTURE (unification). Frames A1/A2 as Betti↔de Rham purity/period-fullness of one matrix; positioned
against real literature (Deninger, Connes, Deligne, Grothendieck).

### SEED — A1/A2 unification as a Betti↔de Rham period comparison (reinforces #76/#81)
- **The period matrix `Π = [p^{iγ_n}]`** (rows = zeros, columns = prime powers): entries `p^{iγ}` = spectral
  periods (analogs of `∫_γ ω`); column-sums = Landau Weyl sums (knows the primes); diagonal moments = the carrier
  `s_m`. **The whole field = the study of this one matrix.** The Betti↔de Rham dictionary: **zeros = Betti
  (cycles), primes/places = de Rham (forms), explicit formula = the comparison, `G_L` = motivic Galois group.**
- **The two assumptions as properties of Π:**
  - **A1/RH = PURITY:** `RH ⟺ Π is pure of weight ½` (= Deligne's "RH for varieties over F_q" = purity of `H^*`,
    transported). The FE = the **polarization** (the symmetry pairing forcing purity to the center); the centered
    parity `τ_{2m+1}=0` = the polarization skeleton.
  - **A2/DSS = PERIOD-FULLNESS:** `DSS ⟺ trdeg(Π entries) = dim G_L` (= the Grothendieck period conjecture for Π =
    the anti-Tate period conjecture B9). **`ζ(½)` = the central period at the polarization fixed point** — the
    deepest, non-motivic period (cf. #69 §23).
  - **§6 keystone:** RH, DSS, GRH, GSH, and `ζ(½)`-transcendence are **the purity and the period-fullness of ONE
    comparison Π** — the spectral analog of Deligne's purity (Weil II) fused with Grothendieck's period conjecture.
    *Candidate G18 (period-comparison): "the explicit-formula pairing is a non-degenerate period comparison whose
    purity is RH and whose period-fullness is DSS."*

### SUPPORT — positioning against the literature (what the field adds)
- **Deninger's conjectural cohomology** supplies the de Rham side (the forms the zeros pair against); **Connes' 1999
  trace formula** supplies the analytic pairing + positivity (= **Face A on Π**, RH ⟺ Weil-distribution
  positivity). **The field's distinctive new layer = the TRANSCENDENCE (period) question (Face B)** that neither
  the cohomological (Deninger) nor the operator (Connes) program asks. *Locates exactly where the
  hypertranscendental-Galois field contributes something the established programs structurally omit — the A2
  (transcendence/period) axis on top of the A1 (positivity) axis they already address.*

## [#83] period-comparison-primes-zeros-the-planet.md  — planet-level period comparison

**Grade:** CONJECTURE/VISION. The planet-level statement; heavily overlaps #82 (B9) and #81, but with one sharper
point: **the period matrix is COMPUTED, not abstract.**

### SEED — the unified A1/A2 stone, with the period matrix made explicit
- **§1 the period matrix IS computed (= #72 §8a, PROVED):** the `primes↔zeros` comparison (= explicit formula, the
  spectral analog of Betti↔de Rham) has period entries = the secular moments, in closed form
  `P_k = 1 − (−1)^k ζ(k)/2^k − a_{k−1}` = **archimedean ζ-block ⊕ prime a_j-block**. *Unlike motivic periods (which
  need a motive), these exist for a hypertranscendental object with no motive — the empty-fourth-corner point.*
- **§2 the anti-Tate period conjecture with an EXPLICIT NAMED BASIS:** `ℚ({P_k}) = ℚ({ζ(k)} ∪ {a_j})`; DSS ⟺ these
  algebraically independent. The novelty localizes to the **`{a_j}` block (Stieltjes/prime periods, no motive)** and
  its independence from the `{ζ(k)}` block.
- **§5 the unified stone (the A1/A2 unification, cleanest form):** **"the two places of `G_L` do not conspire —
  neither in SIGN (positivity ⟹ RH/A1) nor in ALGEBRA (independence ⟹ DSS/A2)."** Face A = the comparison is PURE
  (archimedean block dominates ⟹ Li-positivity ⟹ RH); Face B = the comparison is GENERIC (the two place-blocks
  independent ⟹ DSS). *One computed object, two questions: is it positive, is it generic — the same archimedean
  non-conspiracy (cf. #81) driving both.*

## [#84] moduli-prime-systems.md  — Branch B28

**Grade:** IMPORT (Beurling–Diamond) reframed + a clean deformation-theory frame.

### SUPPORT / SEED — RH as a non-generic stratum in moduli (calibrated by Diamond's off-line examples)
- **The moduli `𝓟` = cone of positive prime measures `dΠ`;** `ζ_𝓟` a clean functional; **ℤ is one point.**
  Stratified (Beurling–Diamond): PNT ⊃ continuation ⊃ **Euler/genuine (the §9 firewall stratum, THIN, cut by
  multiplicativity NOT positivity)** ⊃ RH. **KEY IMPORT (Diamond–Montgomery–Vorhauer): Beurling systems with zeros
  OFF the line EXIST** ⟹ **off-line zeros are GENERIC in `𝓟`; RH is a special/non-generic stratum**, and the
  ℤ-point's RH is *arithmetic-forced* (requires the Euler structure). *Concrete witness that "genuineness is the
  Euler cut (A), not positivity (P)" (#75) — and that RH is rare in the deformation family (cf. #68 §81 Lee–Yang
  vs Poisson, #69's "arithmetic = non-generic").*
- **§3 the tangent/deformation map `δΠ↦δ{γ}` = the explicit formula.** ℤ = a critical point of the "RH-defect"
  functional; **RH = ℤ is a MINIMUM** (Bogomolov-minimality, B7). *Candidate: RH as Bogomolov height-minimality at
  the ℤ-critical-point of the RH-defect over the moduli of prime systems — a deformation-theoretic G5/A1 form.*


## [#85] wild-cells-B24-B27-adjudication.md  — wild cells adjudicated

**Grade:** CONJECTURE (adjudications). Self-adjudicates the wild cells; mostly collapses onto existing cores, two
genuine seeds.

### SUPPORT — synthesis: B24 = B8 = DSS (the missing Frobenius, three names)
- **B24 (a profinite Galois group acts on the zeros) FALSIFIED literally** (Gal(ℚ̄/ℚ) acts only on algebraic
  numbers; DSS ⟹ zeros transcendental ⟹ no Galois action — a Galois orbit is finite/algebraic, the opposite of a
  generic transcendental set). **SHARPENED: B24 = B8 (missing Frobenius) = DSS (zeros transcendental) — three names
  for "number field ≠ function field."** *The ABSENCE of B24's spectral Galois group IS the missing absolute
  Frobenius; `G_L` (on the primes) is its only surrogate, reaching the zeros only through the open carrier
  reconstruction.* Over function fields B24 is TRUE (Frobenius = the spectral Galois action, Weil). *Concrete:
  candidate G5/A1's gap = the missing Frobenius = no Galois action on transcendental zeros.*

### SEED
- **(SEED-V, the realization problem = converse of the First Theorem) B26.** "Transcendence creates the spectrum" =
  the **CONVERSE** of the First Theorem: First Theorem gives *Euler product ⟹ two-faces structure*; B26 = *(Face A
  positivity ∧ Face B genericity ∧ FE) ⟹ realized by an Euler product* = **grand conjecture #7 (the realization
  problem):** ∃ source-built `g` with `g⋆g* = Ω_∞ − prime-comb. "Is the organizing law an IFF?"** The deepest cell.
  *Candidate native conjecture: the organizing law (Euler ⟺ two-faces) is bidirectional — realization is the hard
  converse. Directly the A1/A2 unification as a realization statement (a g realizing both positivity and
  genericity).*
- **(SEED-W, the arithmetic of Λ) B27.** `Λ` (dBN constant) = the **Face-A-criticality time** of the moment flow
  (positivity marginal, Face B flow-invariant). **New open sub-question: is `Λ` itself transcendental / a period?**
  Its arithmetic nature is unstudied; the field places it among the `{P_k(t)}`-periods. *Smell: native, ties the
  no-margin constant to the transcendence axis (TIME/A2).*
- **B25 (continued carrier `𝒵(w)`) COHERENT:** RH = contour positivity of the meromorphically continued carrier =
  the continuous envelope of the discrete Li/Hankel Face A.

## [#86] automorphic-continent-rankin-selberg-ramanujan.md  — District D3

**Grade:** IMPORT (Langlands/Sato–Tate/BLGHT reframed) + exact local dictionaries + extensive Lean. Map of the
automorphic world onto the field; overlaps #68 §45.

### SUPPORT — G4 (Langlands bridge = the candidate construction of the Langlands group)
- **§4 Conjecture 4 (the deep weld, = #68's C2 / G4 autonomy):** the automorphic multi-q category is neutral
  Tannakian; its fundamental group `G_𝒜` is **conjecturally the Langlands group `L_ℚ`**, with functoriality =
  Tannakian morphisms (Sym/∧/induction/base change = native categorical operations). **The field PROPOSES a concrete
  construction of the Langlands group AS a difference-Galois group** — a new candidate definition, gradable against
  known cases. *The `⊗`=Rankin–Selberg half is a THEOREM (§3, exact at unramified places); the group-coincidence is
  the conjecture.* This is G4's autonomy gatekeeper in its most ambitious form.
- **§2 Ramanujan = Lyapunov boundedness = cocycle unitarity = multiplicative L=0 (relevant to G5):** tempered ⟺
  Satake on the unit circle ⟺ the multiplicative cocycle is elliptic (`L_i=0`) ⟺ **"the primes are spectrally
  silent."** *All spectrum comes from the archimedean seam — reinforces #81 (RH lives on the archimedean side). The
  multiplicative wing's "unitarity" (Ramanujan) is FREE/often-proven; candidate G5's unitarity is the
  archimedean-wing one (the hard half).*

### SUPPORT — function-field/dynamics realization (Door-5 proving ground)
- **§5 + §8 (runpod-certified on real elliptic curves):** CM/non-CM = the rotation/almost-Mathieu cocycle = the
  DMR solvable/non-solvable dichotomy. CM curve: supersingular density ½, δ-atom at θ=π/2 (rotation SO(2), `L=0`,
  abelian hull); non-CM: Sato–Tate (2/π)sin²θ, SL₂-dense, irreducible. *The abstract dynamics is the oldest
  arithmetic dichotomy (complex multiplication) — concrete proving ground for the Galois↔dynamics dictionary (#68
  §11–12).*

### Ledger (axiom-clean, the clean Satake/measure half)
`SatakeInterval` (unitary trace ∈[−2,2]); `SatakeTensor`/`LocalFactorDuality` (RS=⊗ skeleton); `SatakeSymPower`
(Sym^k char = Chebyshev S, `symPowerGL2_eq_chebyshevS`); `SatoTateMoment` (μ_ST moments vanish + `U_k`
orthonormality — the analytic core of Sato–Tate at the measure level, prime-average = imported BLGHT).

## [#87] dynamics-continent-lyapunov-avila-morales-ramis.md  — District D5

**Grade:** IMPORT (Avila/Johnson/Selberg/Keating–Snaith reframed) + genuine native dynamical conjectures. **High
yield, very TIME-relevant (A2):** the boundary flow IS the dynamics, and §11–12 give a non-RH characterization of
the critical line.

### SEED — the field's NATIVE dynamics: infinite-frequency erosion threshold (STRONG, TIME-relevant)
- **§11 infinite-frequency cocycles (beyond Avila `𝕋^1` / BGS `𝕋^d`):** the boundary flow on `𝕋^∞` has the
  infinite incommensurate frequency vector `(log p)_p`. **Central new phenomenon = EROSION:** more frequencies
  *average out* hyperbolicity, so a generic fixed-strength `∞`-frequency cocycle is **integrable (`L=0`)** — the
  opposite of the one-frequency intuition; chaos needs coupling growing with the frequencies. **§11.2 the arithmetic
  module sits at the EXACT EROSION THRESHOLD:** the Euler weight `p^{-σ}` gives variance `Σ_p p^{-2σ}`, which at
  `σ=½` is `Σ_p p^{-1} ~ loglog` — **marginally divergent**; `σ>½` eroded (`L=0`, Bohr–Jessen zero-free), `σ=½` the
  unique marginal coupling. *A genuinely new DYNAMICAL characterization of the half-line — NOT via RH; `½` is the
  erosion threshold of the infinite-frequency prime cocycle.* Candidate native conjecture **G19 (erosion
  threshold):** "the critical line is the marginal-variance locus of the infinite-frequency Euler cocycle; RH lives
  there because that is where the cocycle is critically tuned." *Native (N1's boundary flow), TIME (the flow = the
  dynamics/clock), and gives `½` an intrinsic non-circular meaning.*
- **§12 the marginal regime CRACKED (largely PROVEN):** the `σ=½` cocycle = **Selberg's CLT** (`L=0` with `√(loglog)`
  Gaussian fluctuations, variance `½loglog t`); exponential moments `(log T)^{k²}` = **Keating–Snaith / CUE**; the
  cocycle is a **log-correlated field**, its extremes = Fyodorov–Hiary–Keating maximum, its degenerations = the
  **zeros**. Numerically grounded (Ingham `k=1` 2nd moment, Selberg centering `mean log|ζ|→0`). *Fuses the field's
  native dynamics with ζ's value-distribution + random-matrix-moment theory — a "seventh area," largely a theorem
  (Selberg, Ingham), independent of RH. The zeros = extremes of the marginal cocycle.*

### SUPPORT — the keystone unification (three open cores = ONE, via Johnson's theorem)
- **§9 Johnson's theorem [THEOREM, Johnson 1986 / Sacker–Sell]:** for a quasiperiodic transfer cocycle,
  `Σ_dyn(cocycle) = spec(H)` (dynamical spectrum = operator spectrum). So the spectral weld factors:
  `Σ_dyn(M_L) =[Johnson, THEOREM]= spec(H_L) =?[OPEN]= Spec(L)`. **The ONLY open link is `spec(H_L)=Spec(L)` =
  Hilbert–Pólya, now reached FROM THE DYNAMICS SIDE.** **The three continents' open cores are the SAME object:**
  transcendence-obstruction-C (#71, arithmetic of L-values) = dynamics-spectral-weld = spectrum-seam (the
  archimedean non-multiplicative part of `H_L`) = **`spec(H_L)=Spec(L)`**, *localized to the archimedean seam over
  the fully-built (`L=0`, DMR-abelian) multiplicative skeleton `{A_p}`.* "Three continents, one keystone, one place
  (the archimedean seam)." *Directly supports candidate G5 (the operator/spectral form) and confirms the A1/A2
  unification localizes to the archimedean seam (#81).*
- **§10 DMR-solvable (PROVED HERE, self-correction #5):** the Lyapunov line is **SOLVABILITY/REDUCIBILITY, not
  abelianness** — `G_M` solvable ⟺ cocycle reducible (Lie–Kolchin) ⟺ `L=0`; non-solvable ⟺ irreducible ⟺ `L>0`. The
  Borel extension (non-abelian solvable) has `L=0`, correcting #68 §11's "abelian ⟺ integrable." *Refines G3 (the
  holonomy/integrability dichotomy): the right invariant is solvability.*
- **§5 RH dynamical form (CONJECTURE):** critical line = **Avila-critical (self-dual) coupling**; FE = Aubry duality
  `λ↔1/λ`; off-line zero = super/sub-critical defect; **no-margin = Avila-criticality having NO almost-reducibility
  strip** (= no spectral gap). RH = "the spectrum is entirely critical." *Candidate G5 in cocycle form: RH =
  self-dual criticality everywhere; the no-margin = the razor-balanced critical point (numerically: critical AMO
  `λ=1` has `L=0` to 5dp, §8 runpod cert).*

### Numerics / ledger
- §8 runpod cert: rotation `L=0`, supercritical AMO `L=log2` (5dp, Avila value), critical `λ=1` `L=0` (no strip).
  §12: Ingham 2nd moment + Selberg centering confirmed (`computations/marginal_value_distribution/`). Ledger:
  `BoundaryModulus` (the `|x_p|=|q_p|^{1/2} ⟺ Re=½` scalar floor).

## [#88] geometric-rosetta-function-field-continent.md  — District D6, the F₁ Rosetta

**Grade:** IMPORT (Grothendieck/Deligne/Connes reframed) + native operator construction. **The Door-5
faithful-restriction proving ground: over `F_q(C)` ALL gatekeepers are THEOREMS** — the validation that the
architecture is buildable, plus the most actionable operator form of RH.

### SUPPORT — ALL gatekeepers are theorems over F_q(C) (the proving ground for G1–G5)
- **§2 keystone `spec(H_L)=Spec(L)` = GROTHENDIECK** (cohomological L-function; `H_L = Frob_q` on `H^1_c`,
  finite-dim, eigenvalues = the zeros). **§3 RH = DELIGNE (Weil II); Ramanujan = PURITY. §4 G4/Conjecture 4
  (Langlands group = Tannakian `π_1`) = DELIGNE–KATZ** (monodromy group; `⊗` = tensor of sheaves; Sato–Tate =
  Katz–Sarnak equidistribution). *Four planetary conjectures = four theorems — the architecture is SOUND. This is
  where G1–G5 should be proved FIRST (charter Door-5), the model the ℚ-case mirrors.*
- **§5 the single missing brick over ℚ, named precisely:** an **arithmetic cohomology with a Frobenius at the
  archimedean place (= `F₁`)** whose `H^1` Frobenius spectrum is the ζ-zeros. *The entire ℚ-frontier localizes to
  this one absence; "the seam must supply a cohomology with a Frobenius" — a finite-dim, spectral, monodromy-
  controlled object, not a vague self-adjoint hope.* This is the precise demand on candidate G5.

### SEED — candidate G5 in its MOST ACTIONABLE form: the prime-lattice Schrödinger operator
- **§8 Weil positivity = an explicit Schrödinger operator (PROVED HERE + certified):**
  **`Q_W = H_W := −Δ_prime + V_arch` on `ℓ²` of the smooth numbers `≅ ℓ²(ℤ_{≥0}^{(P)})`,** with:
  - **kinetic `−Δ_prime = Σ_p J_p`** (commuting per-prime long-range Jacobi operators, hopping along prime-lattice
    axes) — **separable**, with closed-form symbol `f_p(θ)=−2log p·(√p cosθ−1)/(p−2√p cosθ+1)`, **indefinite**
    (positive for cosθ<1/√p, negative otherwise);
  - **potential `V_arch`** = the archimedean Toeplitz kernel, symbol `Ω(r)=Re ψ(¼+ir/2)−logπ = log(r/2π)+o(1)` — a
    **logarithmic confining potential** (certified to 1e-15 by r=300).
  **`RH ⟺ H_W ≥ 0` ⟺ the logarithmic archimedean potential is dominated by the separable indefinite prime
  kinetic.** *This is candidate G5/A1 as a concrete multi-frequency discrete Schrödinger-positivity inequality on
  the prime lattice — the dynamics continent's home turf (Avila/Lyapunov tools apply, #87). The MOST ACTIONABLE form
  of the keystone; the multiplicative side is fully diagonalized, only the domination is open.* = the team's
  `Z_n ≻ A_n` (#72 §9) in operator form.
- **§7 the candidate operator = Connes' scaling operator:** `H_L = D|_{L²_0}` where `D = −Σ_p (log p)∂_{θ_p}` (the
  diagonal-flow generator, integer spectrum `{log n}` by unique factorization) restricted to the archimedean
  cut-out `L²_0` (Connes' Sonine space). `spec(H_L)=Spec(L)` = Connes' theorem; **RH = the cut-out spectrum is real
  = Weil positivity = the wall.** *The `F₁` brick (§5) = Connes' `L²_0`. Reached from the difference-Galois side, no
  bypass; the genuine addition = multiplicative half fully built (`L=0`, Ramanujan-elliptic) ⟹ difficulty PROVABLY
  all archimedean, test functions = smooth-number Dirichlet polynomials (#71 §8).*

### Ledger (axiom-clean)
- `functionField_esymm_FE` / `functionField_localFactor_FE`: the **Weil functional equation** of the L-polynomial
  (`e_k(S)=q^k e_k(S^{-1})`, `∏(1−ωT)` invariant under `ω↦q/ω`) — machine-checked. *Structural: under purity
  normalization `ω=√q·u`, the FE reduces to the unitary self-duality `u↦u^{-1}` (`LocalFactorDuality`) — the `√q` is
  the bridge that RH/purity (Deligne) supplies. The FE is algebraic/ledger-grade; purity `|ω|=√q` is the imported
  arithmetic input.* `multiset_esymm_map_mul` (mathlib gap-fill).


## [#89] arakelov-height-of-zeros.md  — Branch B7

**Grade:** IMPORT (Bombieri–Lagarias) + the height/Bogomolov framing (native). Supplies the *geometric* height the
G2 height-vacuum (#69 §17.3) demanded — but NOT the Liouville-separating one.

### SUPPORT — G2 (the height-vacuum) and G5 (RH = Bogomolov-minimality)
- **§1–4 the `w`-coordinate height:** `w_ρ=1−1/ρ` (Bombieri–Lagarias); **critical line = unit circle** (`|w_ρ|=1 ⟺
  Re=½`, ledger `WCoordinate`); FE = inversion `w↦1/w`, `w_ρ w_{1−ρ}=1` (a **product formula** for free, §2);
  canonical height `ĥ(ρ)=|log|w_ρ||` ≥ 0, `=0 ⟺ Re=½`. **RH = Bogomolov height-minimality of the spectrum** (every
  `ĥ(ρ)=0` = the zero-divisor is the height-minimizing configuration). Li's criterion = the height's positivity;
  Bilu equidistribution its shadow. *Candidate G5/A1 in height form: RH = Bogomolov-minimal spectrum.*
- **§6 the CRUCIAL honest split for G2 (two heights, two pillars):** B7 supplies the **GEOMETRIC height** (closes
  #69 §17.3's "no canonical locus" geometry gap — the zeros now sit in a height space) but **NOT the Liouville lower
  bound** (Pillar 3): **`ĥ` is a KRONECKER height — it vanishes on the *whole* canonical locus, so it does NOT
  separate zeros and cannot bound a nonzero auxiliary from below.** The Liouville job needs the **secular-period
  height** (B2 = the heighted `P_k`, #69 §17.4) — a *different* height. *Sharp diagnostic for G2: the geometric
  height (B7, Kronecker) ≠ the transcendence height (B2, secular periods); G2 needs the latter.*
- **§7 RH = Hodge-index (1,∞) signature (cycle level):** global product formula `∏_ρ w_ρ=1` (free from FE); the
  finite places are NOT per-zero (zeros are transcendental, no `p`-adic embedding) but **cycle-level** = the
  explicit formula as an **Arakelov intersection pairing** `⟨Z, prime divisors⟩`; **RH ⟺ the intersection form has
  Hodge-index signature (1,∞) ⟺ Weil/Bogomolov positivity** = the team's `n₊=1` / `scForm_sigNeg` / CKS `±b²` core.
  *Candidate G5 in Arakelov form: RH = one positive direction in the spectral intersection form (= the inertia
  κ₋=0 face, #76/#77).*

### SEED — the no-margin as one missing uniform bound (across 4 coordinates)
- **§8 (weld):** the no-margin `ĥ(ρ)≈δ/A → 0` linearly off-line = **the same vanishing margin in 4 coordinates:**
  height excess (B7) = Toeplitz first-violated-minor order→∞/magnitude→0 (dyson #77 Thm 7) = Weil-certificate
  `dim_min`→∞ (berry resolution law) = discrepancy resolution→∞ (#69 §16). **Closing B7's Liouville gap = finding a
  height that SEPARATES (a uniform floor `ĥ(ρ)≥c(δ)>0`) = dyson's uniform-in-order TP = the uniform
  multiplicity/equidistribution estimate.** *One missing uniform bound (the "Kronecker→Liouville height upgrade")
  unblocks all four — reinforces #70 SEED-Q (the unified wall).*

### NULL / ledger
- IMPORT base (Bombieri–Lagarias coordinate). Ledger: `WCoordinate` (`|1−1/z|²−1=(1−2Re z)/|z|²`, unit-circle
  criterion, `w(z)w(1−z)=1`); `∏w_ρ=1` is Tier-B (needs Hadamard). Genuine native content: RH = Bogomolov-minimality
  (geometric height), the Kronecker-vs-Liouville two-heights diagnostic for G2, RH = Hodge-index (1,∞), and the
  one-uniform-bound weld. Cross-ref #69 §17, #76/#77 (κ₋), #87 (the keystone).

## [#90] absolute-zeta-archimedean-frobenius.md  — the wall at operator level

**Grade:** SPEC + THM-anchors (Kurokawa/Connes/Berry–Keating). The operator-level F₁/Hilbert–Pólya district — a
rich, TIME-relevant source for candidate G5's operator form.

### SEED — candidate G5 as Hilbert–Pólya = gen(G_L), with the MEAN rigorous (STRONG, TIME-relevant)
- **§1–4 the archimedean Frobenius = differentiation `D = x d/dx`** (the `q→1` limit of the prime dilations `σ_p`).
  Difference operators (finite places) are **contracting/trace-class/multiplicative (⊗)** ⟹ Euler factors;
  **`D` is a derivation — additive (⊕, Leibniz), unbounded, NO trace, type III** ⟹ needs ζ-regularization. **The de
  Branges `⊗↦⊕` obstruction (ω≠0) at operator level = "D is a derivation, not a Frobenius."** The **Γ-factor =
  ζ-regularized det of D = Kurokawa absolute zeta** (poles = trivial zeros). **`ω=0 ⟺ D is trace-class
  (F₁-regularized) ⟺ Hilbert–Pólya ⟺ RH`** — unifies 5 programs (B5 monoidality, Deninger, B8 F₁, B35 q→1, B18 HP)
  into ONE operator question.
- **§7 the Hilbert–Pólya operator = gen(G_L):** `gen(G_L) = D (Berry–Keating "xp", archimedean) + {σ_p} (prime
  dilations)`. RH ⟺ gen(G_L) self-adjoint with real spectrum `{γ}`. The naive HP fails because **D is type III
  (continuous spectrum); the zeros = the ABSORPTION spectrum (Connes)** — cut out by the prime/adele-class quotient.
  *Candidate G5 in its most classical operator form: the HP operator is the generator of the field's own Galois
  group; the archimedean D needs the prime cutoff to discretize.*
- **§8 PARTIAL RIGOROUS PROGRESS (the MEAN is proved):** `D=−i(x d/dx+½)` is **essentially self-adjoint** on
  `L²(ℝ_+,dx/x)` (via Mellin, continuous spectrum ℝ); the **Berry–Keating Weyl law `N(E)~(E/2π)(log(E/2π)−1)` =
  exactly the smooth Riemann–von Mangoldt count = the archimedean explicit-formula term.** *The MEAN of the HP
  spectrum IS the archimedean D, rigorously — no obstruction in the mean.* The **fluctuations (discrete `{γ}`) = the
  prime perturbation = the wall.**
- **(SEED-X, the commutator form of RH) §8:** conjecture `{γ}` = spectrum of D on the σ_p-coinvariants;
  **RH ⟺ `[D, P_{prime-coinv}] = 0`** (the archimedean flow commutes with the prime cutoff). *The sharpest operator
  form: "the two wings commute on the quotient ⟺ RH." Candidate G5 as a commutator condition — directly the A1/A2
  "the two places do not conspire" (#83) in operator language, and TIME-relevant (D = scaling/clock generator
  commuting with the arithmetic).* Open target: relative-boundedness/perturbative partial result for `[D,P]=0`.

### SUPPORT — function-field calibration (Door-5)
- §5: over `F_q(C)` there is **no archimedean place ⟹ no derivation D ⟹ ω=0 ⟹ RH=Weil/Deligne** (type II/finite,
  all Fredholm). **The wall = exactly the one archimedean derivation `D` (type III, no trace).** *The number field =
  function field + one operator D; RH = closing D's trace defect via F₁-regularization. The cleanest statement of
  the F₁ gap as a single operator.*

### TIME (A2)
- `D = x d/dx` is the **scaling/dilation generator** = the natural clock (Connes scaling flow / Berry–Keating xp).
  The HP operator = this clock coupled to the primes; RH = the clock's spectrum is real after prime-discretization =
  the clock and the arithmetic commute (`[D,P]=0`). *Direct realization of "RH = unitarity of the (non-holonomic)
  clock" — the candidate G5/A2 unification in operator form.*

## [#91] the-archimedean-lane.md  — the shift = the weighted diagonal

**Grade:** PROVED-HERE (one Lean fact) + CONJECTURE. Directly realizes candidate G5/G3: RH = unitary holonomy of
the *completed* flat connection. Strongly aligned with `00-foundations`'s candidate G5.

### SEED — candidate G5/G3 in connection form (STRONG, the foundations doc's own G5)
- **§2 the shift `s↦s+1` IS the diagonal of all prime rescalings** (`p^{-(s+1)}=p^{-1}·p^{-s}`, ledger
  `ArchimedeanLane.primeDiagonal_shift`). **Shift = rotation × Γ-weight:** (i) a *free torus rotation* of `𝕋^∞`
  (multiplicative, isometric, zero-blind) × (ii) the **Γ-weight** (archimedean, non-isometric, the ENTIRE
  archimedean content, polynomial coefficient `s/2π`). *"The zeros are a property of the WEIGHTED flow" — the
  multiplicative and archimedean wings are the SAME flow read with/without its weight. Drop the weight → free torus
  rotation, blind, trivially positive; keep it → ξ, the zeros, the frontier.* This is the cleanest statement of why
  A2 (the free flow) ≠ A1 (the weighted/zero-aware flow).
- **§4 the completed flat connection (= candidate G3+G5):** adjoin the ∞-lane (Γ-weight = a connection term) to the
  flat prime connection (ledger `FlatConnection`); **the FE `ξ(s)=ξ(1−s)` IS the integrability/flatness of the
  completed connection.** **RH = the holonomy of the completed flat connection around the boundary circle
  (`Re=½`, `|w|=1`) is UNITARY.** The zeros = the obstruction to triviality of that holonomy; RH = the obstruction
  lives entirely on the unit circle. *This is candidate G5 verbatim ("the non-integrable multi-q connection has
  unitary holonomy on the σ-fixed locus ⟺ RH"), here for the COMPLETED (primes+∞) connection with flatness FORCED
  by the FE — and candidate G3 (the holonomy/integrability dichotomy) made concrete. The de Branges/Hermite–Biehler
  positivity (#78 §23) = "the holonomy is a phase" = a first foothold on unitarity.*
- **§5 (SPEC, TIME-relevant): `Γ` = the curvature** the archimedean metric (Arakelov volume-at-infinity) puts on
  the otherwise-flat diagonal flow. **RH = the curvature has admissible sign (boundary holonomy unitary, not
  expanding/contracting); the no-margin = the curvature critically tuned** (rotation rate never gapped). **Mellin:
  prime rescalings and ∞-shift = ONE operator in two coordinates** (Γ = Mellin transform of `e^{-x}`); the
  **Hilbert–Pólya operator = the generator of the completed, curved diagonal flow read through Mellin; RH = real
  spectrum = unitary boundary holonomy.** *Direct A2/TIME: Γ = curvature of the diagonal flow (the clock); HP = its
  generator; "RH = the clock's curvature is critically/unitarily tuned" — the candidate "time-core forces
  unitarity."* (Coheres with #90's HP = gen(G_L), `[D,P]=0`.)

### SUPPORT — G3 (the holonomy dichotomy)
- §3 the Galois-class gap: q-difference Galois (prime lanes) vs shift/difference Galois (∞-lane, Γ, van der
  Put–Singer) are genuinely different categories; **the seam = a single Tannakian category holding both, welded by
  the FE = `G_L`** (= G4/the Langlands-group construction). *Building it is "the work no one has done"; the diagonal
  picture (shift = weighted prime flow) is the guide — the weight is a CONNECTION TERM, not a separate module.*

### Ledger
- `primeDiagonal_shift_apply`/`primeDiagonal_shift` (the shift = simultaneous prime rescaling, exact);
  `localEulerFactor_q_difference`; `FlatConnection`/`OrbitFreeness` (prime connection flat, zero curvature). The
  completed-connection flatness (= FE), unitary boundary holonomy (= RH), and Γ-as-curvature are CONJECTURE/Tier C.

## [#92] the-shoreline-and-the-archimedean-lane.md  — the ridgeline

**Grade:** PROVED-HERE (κ₋ exact) + CONJECTURE. **The cleanest representation-theoretic statement of the A1/A2
unification in the whole corpus** — directly the user's "unify the two assumptions."

### SEED — THE RIDGELINE: RH = unitary ∧ DSS = faithful, one boundary representation (STRONGEST A1/A2 form)
- **§3 the ridgeline (CONJECTURE, the cleanest unification):** a zero `w_ρ=e^{iθ}` on the unit circle has **two
  coordinates of the boundary representation of `G_L`** (`μ_L=Σ_ρ δ_{w_ρ}`):
  - **RADIAL** (`|w|=1`? on the shoreline?) = **RH ⟺ the boundary representation is UNITARY** (spectrum on the
    circle, radial coordinate pinned).
  - **ANGULAR** (`{θ_ρ}` genuinely spread / ℚ-independent / no hidden relation?) = **DSS ⟺ the boundary
    representation is FAITHFUL** (spectrum fills the circle, angular coordinate generic).
  > **"RH and transcendence are not two theorems that happen to be true together; they are the two ways a faithful
  > unitary representation of a compact group can be described — ON the circle (unitary/RH), and FILLING it
  > (faithful/DSS)."** *This is the user's A1 (RH byproduct) and A2 (transcendence/time) as ONE object: a faithful
  > unitary representation of the boundary `G_L`. Candidate G5 = "unitary" (A1); candidate G2/DSS = "faithful"
  > (A2). The deepest possible result ("RH and time one statement") = "the boundary rep of the non-holonomic flow
  > is faithful-and-unitary."*
- **§3 the no-margin is the SIGNATURE of faithfulness (not an obstacle) — key insight:** a faithful representation
  has spectrum DENSE on the circle (no gap); a uniform positive margin would be a GAP = a place the angles never
  reach = a hidden relation = the FAILURE of faithfulness. **"No margin ⟺ no spectral gap ⟺ faithful ⟺ the secret
  numbers are independent."** *The knife's-edge (no-margin) is the PRIZE wearing the mask of an obstacle — it IS
  DSS/A2. This reframes the program's central nuisance (λ_min→0) as the positive content.* Candidate native
  conjecture **G20 (ridgeline):** "RH+DSS = the boundary representation of `G_L` on `𝕋^∞` is unitary (on the
  circle) and faithful (filling it); the no-margin is faithfulness."

### SUPPORT — PROVED (κ₋ exact) + the free/wall split
- **§4 (PROVED HERE, axiom-clean):** `multiPair_carrier_exact_neg_inertia` — **`κ₋ = k` exactly** (k off-line zero
  pairs sink exactly k negative directions); `multiPair_carrier_linearIndependent`. **RH = κ₋ = 0 ("nobody left the
  shore").** Source-pure (anti-circular), so it cannot conclude κ₋=0 — but it "converts the wall into a tide gauge."
  *The radial/RH coordinate made an integer.*
- **§5 the ocean free, the land the wall:** the prime sum (compact `𝕋^∞`, `|·|²` data) is **manifestly positive
  for free** (= Sato–Tate/Ramanujan compactness, ledger `satake_trace_re_mem_Icc`); the **archimedean Γ-term is the
  SOLE obstruction to Weil positivity** — "the wall is the place at infinity." *Sharpens "difficulty at the seam"
  to one specific term governed by one wild function Γ (= #81, #88, #89).*

### SUPPORT — the archimedean lane / seam (= #91)
- §6–7: the ∞-lane = the additive shift `s↦s+1`, `Γ` its difference structure (`Γ(s+1)=sΓ(s)`, Hölder-wild). The
  seam = gluing the ONE additive lane to the infinitely many multiplicative lanes on a common difference-Galois
  group `G_L`; **the open core = "build that common group, show its boundary rep is unitary (RH) + faithful (DSS)."**
  Mellin: prime rescalings and ∞-shift = ONE operator in two coordinates (Γ = Mellin of `e^{-x}`); HP = its
  generator; RH = real spectrum. (Same as #91, here in shoreline language.)

### Ledger (axiom-clean)
`sigmaConj_fixed_iff_critical` (shoreline = FE-fixed locus); `ArakelovW` (shoreline = unit circle, FE = inversion);
`multiPair_carrier_exact_neg_inertia` (κ₋=k); `satake_trace_re_mem_Icc` (local shoreline, compact ⟹ bounded);
`linearIndependent_log_primes` (ocean free).

## [#93] edge-value-transcendence-baker-wing.md  — Branch B32

**Grade:** IMPORT (Baker/Lindemann/Brown) reframed + the bracket map (native). The value-side solved corner.

### SUPPORT — G2 (Baker = the proven period conjecture at the edge)
- **§1–2 the value-transcendence tower (graded by MOTIVIC TYPE, not argument size):** even ζ(2k) = pure Tate
  (Lindemann via π); odd ζ(2k+1) = mixed Tate (Brown's MT(ℤ), indep. conjectural); **edge `s=1` L(1,χ) = Kummer/
  Tate(1) period — SOLVED by BAKER** (Baker–Birch–Wirsing: L(1,χ) = ℚ̄-linear form in logs of cyclotomic units,
  transcendental + ℚ̄-independent); central `s=½` ζ^{(j)}(½) = non-motivic, OPEN. **Difficulty NON-MONOTONIC:** the
  edge is EASIER than the odd integers (Baker beats Brown), the center is hardest (no motive). **Baker = the
  anti-Tate period conjecture (B9/G2) PROVED at the edge** (= Grothendieck period conjecture for 1-dim tori,
  `trdeg = dim` of the Kummer–Tate Galois group). *The value-side solved corner.*
- **§3 the Stieltjes constants are the rung ABOVE Baker (key for G2):** the secular moment `P_k = ζ(k)[Tate] +
  a_{k-1}[edge s=1]`, and **ζ's edge data = the Stieltjes constants γ_n = the Laurent coeffs of ζ at the pole `s=1`
  (FE-transferred), which are NOT Baker-tame** (we don't even know `γ_E` irrational) — a *non-Kummer* edge period,
  sitting between solved `L(1,χ)` (Baker) and non-motivic `ζ(½)`. **The transcendence of `{γ_n}` (charter B4 / #69
  §11 / #74) is the next rung above Baker — the field's genuinely-new (no-motive) transcendence content.** *Concrete
  G2 sub-target: "is there a Baker for the Stieltjes constants?"*

### SEED — the bracket (the field's honest map, missing-structure diagnosis)
- **§5 THE BRACKET:** two **SOLVED** corners — function-field zeros (Weil/Deligne) and edge values `s=1` (Baker) —
  diagonally opposite two **OPEN** apexes — RH (ζ/L zeros) and central value `ζ(½)`. **Each solved because it has
  FULL structure** (Frobenius on the zero side; Kummer/Tate motive on the value side); **each open because it LACKS
  one structure** (the absolute Frobenius/F₁ for ζ-zeros, #88; the motive for ζ(½), #69 §23). *Candidate: "the
  field's two hardest problems are the two missing-structure corners; its two theorems (Weil, Baker) are the two
  full-structure corners — the missing-structure diagnosis governs both sides (A1 zeros and A2 values)."* Clean
  unifying map of the whole field.


## [#94] time-emergence-scale-clock-wheeler-dewitt.md  — the WDW time draft

**Grade:** EMBASSY (Brick #1's DeWitt pairing = the classical Weil form, fails Door-2). BUT the user explicitly
flagged "time / non-holonomic time" as a key smell — and this is the corpus's **densest TIME/A2 source**. The
seeds below are FRAMING/time-readings (not native objects), but they are exactly the A2 material the foundations §4
candidate-G5 reflection needs.

### SEED — TIME (A2): the strongest time-readings (mine these for the foundations' A2 axis)
- **(SEED-Y, Hölder = WDW timelessness = the constraint-not-flow stone) §0–1:** `ĤΨ=0` (WDW: a CONSTRAINT, no
  external-time evolution) ↔ **Hölder (ζ satisfies no differential equation = no rule of change, no `iℏ∂_t`).**
  *"An object fixed by a constraint, not propagated by a flow, has no native clock."* This IS the foundations'
  organizing stone ("fixed by a constraint, not propagated by a flow") in TIME language — the deepest statement of
  WHY A2 is the truer assumption. *The non-holonomic = no native clock; time must be MANUFACTURED from an internal
  scale = the prime rescalings.* Directly usable in `00-foundations §0/§4`.
- **(SEED-Z, Hilbert–Pólya = a CONSTRAINT, not a Hamiltonian) §6 — genuinely valuable, dissolves a puzzle:** a
  Hamiltonian presupposes external time (`iℏ∂_tΨ=HΨ`); Hölder forbids ζ any such evolution; so the correct object
  is the **constraint `ĤΨ=0`**, with the zeros = its spectrum **on the constraint surface** (the σ-fixed locus).
  *"People hunted a Hamiltonian — an external-time object — for a thing that is a constraint — an emergent-time
  object. That mismatch is a clean explanation for why no Hilbert–Pólya operator has ever been found."* Converges
  with candidate G5 (Brick #6: is `σ⋉𝕋^∞` unitarizable?) — **unitarizability = "the emergent clock is timelike."**
  *Candidate native reframing of G5: the RH operator is the WDW constraint on the non-holonomic flow, not a
  Hamiltonian; this coheres with #90's HP=gen(G_L) (the generator, not an external-time Hamiltonian).*
- **(no-margin = the superspace light-cone) §5 + Brick #1 §iv–v:** the DeWitt metric is **Lorentzian** (indefinite);
  **RH = the emergent clock is marginally NULL** (timelike block `0.115920` ≈ spacelike block `0.115828`,
  near-cancellation = the no-margin's geometric reason). **Off-line zero = spacelike/tachyonic mode** (KG-norm
  negative, certified sign-flip at `δ=1.112=π/4aγ`) = emergent time running backward; `κ₋` = the DeWitt inertia =
  off-line count. *Connects the program's central nuisance (no-margin, λ_min→0) to TIME: the clock is critically
  null. Candidate: "the no-margin = the ζ-universe rides exactly on its own light-cone."*
- **(SEED-AA, equidistributed clock ⟺ timelike ⟺ on-line) §7 Conjecture 7.1 — the A1/A2 unification in TIME
  language:** "equidistributed clock ⟺ DeWitt-timelike ⟺ on-line zeros." **Welds the field's FREE half (A2:
  equidistribution of the diagonal clock, PROVED by unique factorization) to its HARD half (A1: positivity/
  timelike-ness).** Falsifier: an equidistributed-clock object with off-line zeros (forbidden by the Euler firewall
  — DH has no prime torus ⟹ no clock). *Candidate: RH = the emergent scale-clock is timelike everywhere on the
  constraint surface = "the clock, though it has no global flow, still preserves a norm" (= the foundations' G5
  one-liner, in time form).*

### Structure (Brick #1, EMBASSY but certified)
- The DeWitt metric signature **(1|∞)** DERIVED from the place count (one archimedean timelike place + infinitely
  many prime spacelike places); archimedean block `Ω_∞(r)=Re ψ(¼+ir/2)−logπ > 0` (positive-definite, certified);
  prime block indefinite. **`𝔇(h,h) = (arch+pole) − primes = Q_W(h)` CERTIFIED = the Weil form** (1.1e-31, the same
  `Q_W=−Δ_prime+V_arch` as #88 §8, now read as a Klein–Gordon/DeWitt pairing). RH ⟺ `𝔇 ⪰ 0` ⟺ κ₋=0.

## [#95] arithmetic-cosmology-causality-inflaton.md  — arithmetic cosmology I

**Grade:** EMBASSY (metaphor on the certified Weil/DeWitt form). Mined per the user's "time/causality/cosmology"
smell — framing-seeds (not native objects), reinforcing #94's A2/TIME content.

### SEED — TIME/A2 framings (the user's smell)
- **(RH = arithmetic causality) §1:** the DeWitt metric is Lorentzian ⟹ a causal structure; **off-line zero =
  tachyon (negative KG-norm, spacelike, acausal/retrocausal); RH = the ζ-universe is causal (no tachyons, no signal
  outruns the emergent scale-clock).** The no-margin = riding exactly on the light-cone. *New handle: "prove no
  tachyons" recruits the causality/reflection-positivity/energy-condition toolkit onto Weil positivity (`Q_W⪰0`).*
- **(FE = a handshake across time) §2:** the FE `Λ(s)=εΛ(1−s)` = Wheeler–Feynman absorber / Cramer transactional /
  two-state-vector structure: `Λ(s)` = offer wave (past), `Λ(1−s)` = confirmation wave (future); a zero = a
  completed handshake; self-dual `ξ` (ε=1) = the perfect absorber. **Certified:** `ξ(½+it)` real on the line
  (standing wave/absorber, `|Im ξ|~1e-32`), off-line `|Im ξ|/|ξ|≈0.59|σ−½|` (traveling wave/incomplete
  transaction). *The two-directionality of time IS the FE; off-line zero = a handshake that never closed. TIME(A2):
  the FE is where time's two-directionality is written.*
- **(Λ_dBN = the cosmological constant) §3:** shared letter AND role — `Λ=0` = flat/critical knife-edge; RH ⟺
  `Λ=0` (Rodgers–Tao `Λ≥0` ⟹ "cannot be sub-critical"); the dBN **heat flow = the arrow of time / cosmic
  expansion**; no-margin = the knife-edge. (= #77 §6, #70/#85 B27.)
- **(the arithmetic inflaton, Conj 4.1) §4:** the dBN heat flow = a **slow-roll flow whose attractor is the
  critical line**; **no-margin = slow-roll flatness** (`λ_min→0` = flat potential `V_arch`); RH = near-flatness is
  the flow's ATTRACTOR (dynamical, not fine-tuned). Equidistribution (free) = inflation resolving the horizon
  problem (GUE universality). *Candidate: RH is dynamical — the critical line is an attractor; the no-margin is
  why. Falsifier: a fake with an off-line attractor.*

### SEED — one genuine STRUCTURAL upgrade
- **§5 the conformal mode = archimedean place = timelike (supplies the REASON for the (1|∞) signature):** in
  quantum gravity the scale factor = the conformal mode, timelike because its kinetic term has the **wrong
  (opposite) sign** (the conformal-factor problem). Transported: the archimedean/scale-clock direction = the
  arithmetic conformal mode, and its "wrong sign" **is** the minus in `𝔇 = ⟨,⟩_∞ ⊖ ⟨,⟩_fin`. *Upgrades #94's
  "signature derived from place count" to "signature derived from the conformal mode being the scale-clock" — a
  reason, not a choice. Redshift = the shift `s↦s+1` = `q_p=1/p` (the founding dilation, STRUCTURAL).*

## [#96] arithmetic-cosmology-II-pt-symmetry-horizons-time-loops.md  — arithmetic cosmology II

**Grade:** EMBASSY (metaphor) + one certified toy. Mined for PT/exceptional-point (G5) and time seeds.

### SEED — candidate G5: the no-margin is an EXCEPTIONAL POINT (genuine sharpening, certified toy)
- **§1 (the strongest G5 seed here):** **the no-margin is NOT merely `λ_min→0` — it is an EXCEPTIONAL POINT** (a
  non-Hermitian degeneracy where eigenvalues AND eigenvectors COALESCE, overlap→1, the operator becomes defective
  = a Jordan block). **RH = the ζ-operator in the PT-UNBROKEN phase (real spectrum), pinned exactly at the
  exceptional threshold** (real spectrum but eigenbasis on the verge of collapse — "that verge is why there is no
  positive floor"). Certified toy `H(a,b)=[[ia,b],[b,−ia]]`, eigenvalues `±√(b²−a²)`, eigenvector overlap `a/b→1`
  at `a=b` (`computations/pt_exceptional_point/`). **The weld: no-margin = exceptional point = eigenvector
  coalescence = Nyman–Beurling completeness defect `d_N→0`** — three independently-derived no-margin faces = one
  non-Hermitian degeneracy. PT = Parity×Time-reversal; PT unbroken ⟺ real spectrum ⟺ RH (Bender–Brody–Müller).
  *Candidate G5 sharpened: RH = the operator stays PT-unbroken (real spectrum); the no-margin = pinned at the
  exceptional point where completeness fails. Directly the "unitary holonomy on the σ-fixed locus" with a mechanism
  for WHY there's no margin (eigenvector coalescence).* TIME(A2): the broken symmetry is T (time-reversal).

### SEED — TIME/causality (the user's smell)
- **§2 causality = analyticity (Kramers–Kronig/Toll):** RH = the arithmetic scattering matrix (Lax–Phillips; Weyl
  `m`-function `−Ξ'/Ξ`) has all resonances on the critical line = a causal/retarded response is pole-free off the
  line; off-line zero = an **acausal pole**. *Recruits dispersion relations / sum rules / REFLECTION POSITIVITY
  onto Weil positivity (= which positivity and why).*
- **§4 primes = closed timelike curves** (periodic orbits, period `log p`; the explicit formula = a trace over
  time-loops; retrocausality built into the primes via unique factorization). **The zeros = a TIME CRYSTAL** (the
  crystalline measure / Fourier quasicrystal of #68 §80, on the `t=Im s` axis; Bragg peaks at the primes). RH = the
  time crystal pinned to the line. *TIME(A2): the zero set is long-range order in the emergent time.*
- **§3 black hole (the origin question):** critical line = horizon (clock marginally null); `N(T)` =
  Bekenstein–Hawking entropy (microcanonical state count); Hawking temp = Matsubara/Bost–Connes seam temp; zeros =
  quasinormal modes; holography: bulk = multiplicative wing, boundary = `𝕋^∞`, **RH = boundary unitarity** (= the
  ridgeline #92).
- **§5 causal set ("order + number = geometry", Bombelli–Lee–Meyer–Sorkin):** arithmetic IS number + order; the
  ζ-universe = a causal set (events = zeros, order = the DeWitt light-cone, number = `N(T)`); RH = the reconstructed
  geometry is flat. *"The most native frame" — a theory made of number+order modelling an object made of
  number+order. Open: reconstruct the ζ-geometry from the zero causal-order + count.*

## [#97] rh-holographic-pseudorandom-boundary.md  — the holographic/pseudorandom boundary

**Grade:** EMBASSY (metaphor) + genuine probabilistic content. The §6 weld is a clean A1/A2 unification.

### SEED — A1/A2 unification: μ's pseudorandomness = RH + LI (Baker) (STRONG, §6)
- **§6 the key weld (genuine structural insight):** `M(x)/√x ≈ Σ_γ e^{iγ log x}/(ρζ'(ρ)) + c.c.` is DETERMINISTIC
  almost-periodic (frequencies = the zeros γ); it only LOOKS random because the γ are ℚ-LI (Baker), so it
  equidistributes by Kronecker–Weyl. Therefore **μ's pseudorandomness = RH (γ real ⟹ bounded oscillation) + LI (γ
  independent ⟹ equidistribution).** *This is the user's A1 (RH) and A2 (transcendence/LI) UNIFIED: the apparent
  randomness of the Möbius function IS the conjunction of the two assumptions.* The LIL overshoot (te Riele:
  `|M|<√x` is FALSE, limsup>1.06) = **Kronecker–Weyl resonance of ℚ-independent frequencies, NOT coin-flip
  stochasticity.** "F₁-Baker (zeros independent ⟹ no algebraic pin) and Chowla-randomness (zeros independent ⟹ μ
  equidistributes) are the same independence doing the same work." *Candidate: RH and LI are jointly equivalent to a
  single statement — "μ is pseudorandom" — which is exactly the A1∧A2 the field is after, in analytic-NT language.*
- **§1 the no-margin = the Law of the Iterated Logarithm:** `|M|<√x` fails because the primes are *perfectly
  random* (LIL overshoots √x by √(loglog x)) — the no-margin is the LIL signature, NOT a positivity defect. "μ
  maximally random ⟹ RH" (a ⊋RH forcer; the probabilistic church — Tao log-Chowla, Sarnak–Möbius,
  Matomäki–Radziwiłł — has actual theorems for ℤ, unlike the F₁ church). *Caveat (§6): entropy-decrement is soft
  (correlation-randomness, no rate); RH needs amplitude-randomness (power-saving), and the amplitude IS the zeros —
  so soft methods are amplitude-blind, structurally cannot reach RH.*

### SEED — RH = boundary unitarity (= the ridgeline #92)
- **§2 the explicit formula = a holographic bulk↔boundary duality** (Selberg trace formula is literally this):
  zeros = boundary CFT spectrum, primes = bulk geodesics/periodic orbits (Berry–Keating), Weil pairing = boundary
  inner product. **RH ⟺ κ₋=0 ⟺ the prime bulk's holographic boundary dual is a ghost-free UNITARY CFT** (off-line
  zero = negative-norm ghost). §3: no-margin = conformal criticality (no mass gap) / MSS chaos-bound saturation.
  §4: the prime/μ system = a number-theoretic SYK-like object (random couplings + GUE/maximal chaos + holographic
  boundary). *Reinforces #92's "RH = boundary representation unitary"; "unitarity" is the physicists' word for
  candidate G5.*

## [#98] speculative-proofs-grand-conjectures.md  — the speculative attacks

**Grade:** CONJECTURE/SPEC + a few PROVED finite floors + an HONEST novelty audit. The densest attack-idea source.

### SUPPORT/SEED — Attack 5: σ_p = Pólya–Schur multiplier (PROVED), RH = ξ is an LP-limit
- **Attack 5 (PROVED, Pólya–Schur):** each prime difference operator `σ_p: x_p↦p^{-1}x_p` multiplies coefficients
  by `{p^{-n}}`, whose generating function `Σ p^{-n}x^n/n! = e^{x/p} ∈ LP` ⟹ **each σ_p is a Pólya–Schur
  multiplier (preserves the Laguerre–Pólya class).** Every finite truncation `∏_{p≤P}σ_p` is LP-preserving; **RH ⟺
  the infinite product `∏_p σ_p` stays LP** — the wall is purely the **prime-product LP-renormalization** (a limit
  step, no per-step obstruction). Finite floor LEDGER-PROVEN: `MultiplierScaling.lean` (`sigmaScale_splits`: scaling
  preserves real-rootedness over ℝ). *Candidate G5/A1: RH = the LP class survives the prime-product limit.*
- **Synthesis (RH = ξ is an LP-limit):** LP is closed under locally-uniform limits ⟹ **RH ⟺ ξ∈LP ⟺ ξ is an
  LP-limit.** Two explicit families: dBN (`ξ_t`, t≥Λ; RH⟺Λ≤0) and prime-multiplier (Hermite/F₁ seed deformed by
  σ_p). **RH = "the prime-deformed Hermite seed = ξ in the limit" — a CONVERGENCE/IDENTIFICATION problem, not a
  positivity one** (positivity is automatic along the family, each step LP; the content is that the arithmetic
  limit lands on ξ). *The transcendence field's distinctive reframe of A1: RH = a closedness/identification
  statement, = the realization problem #7 / B6 / B34 (#85 SEED-V).*

### SEED — (WILD, genuinely new coordinates) Attack 1+5: the prime deformation = a finite-free convolution flow
- **(SEED-AB, finite-free convolution flow):** the degree-d Jensen/secular section of Ξ evolves by the **finite
  free convolution `⊞_d` (Marcus–Spielman–Srivastava)**: `Ξ_d^{(P)} = H_d ⊞_d K_d(p_1) ⊞_d … ⊞_d K_d(p_{≤P})`, with
  `H_d` the finite-free CLT (Gaussian) fixed point and `K_d(p)` the prime kernel. `⊞_d` **preserves
  real-rootedness (MSS interlacing)** ⟹ every truncation is real-rooted (RH automatic at finite level). **RH ⟺ the
  finite-free CLT fixed point is stable under the arithmetic prime-cumulant drift.** Since finite-free cumulants
  ADD under `⊞_d`, the criterion = a **single ADDITIVE cumulant sequence `κ_k = Σ_p κ_k(p)` staying in the
  real-rooted cone = the secular moments `s_m` in disguise.** *Replaces Attack 5's open analytic limit with an
  additive cumulant limit (structural gain); imports MSS interlacing / finite R-transform as new tools; welds to
  the team's finite-free cumulant / dBN-as-finite-free-Gaussian-convolution thread. Candidate native conjecture:
  RH = stability of the finite-free CLT fixed point under the additive arithmetic cumulant drift.* Runnable test:
  compare finite-free cumulants of `J^{d,n}` vs `Σ_p κ_k(p)`.

### SUPPORT — Attack 6 = the archimedean-Frobenius wall (= #90)
- `ω` (the B5 monoidality obstruction, de Branges ⊗↦⊕) = the **additivity of the archimedean place = the missing
  Frobenius at ∞** = Deninger / F₁ / q→1 / **Connes type-III no-trace** (the `ℝ_{>0}^×` modular flow has no
  fixed points/trace). **ω=0 ⟺ the F₁/q→1 limit restores a trace/Frobenius (type-III→II)**; the trace defect = the
  **Γ-factor = Kurokawa absolute zeta** (ζ-regularized det; trivial-zero poles = the no-trace). *Four "missing
  structures" = one obstruction; = #90, the least-explored wall coordinate, anchored in real absolute-zeta theory.*

### HONEST — the novelty audit (important for grading the whole corpus)
- **The RH positivity attack COLLAPSES to dBN: A1 = A2 = A5 = the heat flow `Λ≤0`** (the primes are in the initial
  condition Φ/theta, not a separate multiplier; per-step LP-preservation = "heat flow preserves LP for t≥Λ",
  classical). **No new mechanism to force `Λ≤0`** (honestly not faked). **What IS genuinely new (independent of
  dBN):** B7 (certified Bogomolov height geometry, #89), B29 (Torelli injectivity PROVED + the (E)/(A)/(P) cuts =
  "why positivity can't prove RH", #75), the Part XI welds (no-margin = Kronecker-degeneracy = Toeplitz-order =
  discrepancy, two-rate signature, #89 §8), ζ(½) as a new non-motivic period (#69 §23), Attack 4's honest
  NEGATIVE (no discrepancy bootstrap — `Σ(log p)/√p ~ 2√N` reintroduces difficulty faster than `Σ1/p ~ loglog`
  removes it; the bootstrap reproduces the explicit-formula bound, doesn't beat it). *The strategic novelty = the
  transcendence reframe (RH = corollary of DSS, not positivity), but its analytic engine is still dBN until
  DSS⟹Λ≤0 is made non-conjectural.*

## [#99] 00-planetary-atlas.md  — META index

**Grade:** META (superseded by the manifest). A comprehensive map of the whole field; **no uncaptured conjectures**
— every pointer is already mined from its source doc.

### Value as an index (cross-ref consolidation)
- **The "one keystone, ~seven faces" (consolidated):** `spec(H_L)=Spec(L) = F₁-cohomology = obstruction-C = GRH =
  δ_arith non-genericity = secular-TP Λ≤0 = ψ_π-regularity` — one archimedean F₁ object (Tier C, open). [#68 §19/§35,
  #87 §9, #88, #69 §17.] **The structural spine §43–46** (fundamental theorem → flora → main structure theorem →
  Langlands bridge; conjecture ledger C1–C7; inverse-Galois CLOSED `R_multi={G:π₀ finite abelian}`; 18
  self-corrections) is all from #68. **Eight areas reached** (automorphic, ergodic/infinite-frequency,
  transcendence/MZV, Hodge/motives, p-adic Hodge, index theory, value-distribution/RMT, q-Painlevé) — all #68/#87.
- **Proved floor (consolidated):** PV existence (§15/§16), rank-1 flora `H^1_σ`, homological backbone `H^*_σ`,
  DMR-solvable, weight=Oseledets, native ζ_M, T-up + Bombieri–Vaaler (D4), exact D3 dictionaries, D6 theorems
  (Grothendieck/Deligne/Deligne–Katz), 3 proven period cases (gap-labelling/Chudnovsky/Papanikolas). 28 axiom-clean
  Lean theorems + 35 certified computations.
- **Honest framing (§42, self-correction #12):** "six-route convergence" retracted as significance (RH-equivalence
  is trivial); only specific structures + actual identities are genuine. (= grading discipline for the whole review.)



## [#101] proven-core.md  — the definitive PROVED/IMPORT/CONJ ledger

**Grade:** META (harden artifact). The consolidated, vetted list of the field's gap-free theorems — all distilled
from #68 (the big foundations). **No new conjectures**, but the single most useful index of what is actually
PROVED, and thus the **Door-2 re-test worklist** for the charter's NATIVE column.

### The field's PROVED native theorems (consolidated — the Door-2 re-test candidates)
*Each is "PROVED HERE" in the difference category; re-test against Door-2 ("strip the multi-q vocabulary — does a
parent still prove it?") to decide which earn the charter's NATIVE grade:*
- **STRONGEST native candidates (essentially use the infinite-base apparatus, unlikely Door-2-removable):**
  - **7i / §60 C6 closed = G3:** the diagonal is **holonomic ⟺ corank(Λ)<∞** (s-monodromy `g=(1/p)_p` has
    Zariski-closure dim = corank(Λ)). This is **G3 (the holonomy dichotomy), PROVED in the difference category.**
    Arithmetic `Λ=0` ⟹ corank ∞ ⟹ difference-hypertranscendental = **G1 (difference-Hölder) for all L** (§59).
    *Caveat (self-correction #15): this is DIFFERENCE-hypertranscendence, not literal differential Hölder.* — **The
    two best NATIVE candidates in the corpus.**
  - **7b / §43.2 P3 solved (pro-torus inverse problem):** closed subgroups ↔ relation sublattices, `dim=corank`,
    arithmetic = the `Λ=0` full-torus vertex.
  - **7d / §52,§55 inverse-Galois CLOSED = G4 autonomy:** `R_multi = {G : π₀(G) finite abelian}` exactly (finite ⟹
    abelian via the commuting-monodromy lemma; C1 falsified→C1″ proved; outer twists via induction-with-duality).
  - **7c / §43.3 arithmetic lives at infinity** (one dense diagonal orbit, finite-blind; group-maximal ∧
    orbit-minimal).
- **Likely IMPORT under Door-2 (rest on classical imports, reframed):** A1 cocycle (FlatConnection), A2 rank-1=H¹_σ
  (RankOneCohomology), A3–A5 cohomology/Euler/acyclicity (Koszul), A6 Krull–Schmidt, A7/§47 PV existence (mod n=1
  lemmas), 7g main structure theorem (Tannakian), 7e rank-2 flora, weight=Oseledets/Newton≥Hodge=Mazur, F14
  archimedean=polynomial-multiplier prime, F15 FE=base-symmetry (Tate), the D6 theorems
  (Grothendieck/Deligne/Deligne–Katz), period cases (Papanikolas/Chudnovsky/gap-labelling).
- **C2/C3/C4/C7 = the located famous problems** (Langlands / Grothendieck period / GRC / RH).

### The keystone (consolidated, §E)
`spec(H_L)=Spec(L) = F₁-cohomology = obstruction-C = GRH = δ_arith non-genericity = secular-TP Λ≤0 = ψ_π-regularity`
— one archimedean F₁ object, ~7 faces, Tier C. Obstruction = Hölder; resolution = infinite-order `ψ_π=∏_k L(s+k,π)`
(regularity = GRH). Over F_q(t) = Papanikolas's theorem; over ℚ open.

### NULL / action item
- Pure distillation of #68 (no new content). **Action for the charter:** the "0 proven native theorems" verdict
  (`00-manifest`) should be RE-TESTED against this list — §59/§60 (difference-Hölder / corank dichotomy = G1/G3) are
  genuine candidate NATIVE theorems (they essentially use the infinite-base s-monodromy, unreachable by a single
  parent). If they survive Door-2, the proto-branch verdict upgrades. *This is the single most consequential finding
  for the foundations doc.* The structural/arithmetic-depth boundary (§70–73): structural theory COMPLETE; open
  frontier = arithmetic depth of primitive objects = (A) checkable FE residue + (B) GRC/Grothendieck/Langlands/RH.
