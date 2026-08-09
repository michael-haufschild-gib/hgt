# Positivity descent and the limit obstruction — field charter

- **ID:** ULF-DESC-1
- **Stage:** 1-in-progress
- **Type:** FROZEN STRUCTURAL LAW / FIELD CANDIDATE
- **Source:** relentless interrogation of ULF-FORK-1's death (local + semilocal positivity are
  free or known; every corpus route and no-go is finite-resolution; only the infinite assembly
  is unclaimed)
- **Status:** [FROZEN] [EXPLANATORY-COMPLETENESS AUDIT PASSED] [FIRST-THEOREM TARGET NAMED]
  [NO LEAN UNTIL THE FIELD DELIVERS A NEW UNCONDITIONAL THEOREM] [NOT RH]

## The frozen law

> **Weil positivity is a descent problem for self-dual cones over the places of ℚ, and its
> obstruction is a pure limit class.** The local data are canonically positive (finite p:
> Herglotz/Tomita — the density is Z_p^{−1}|ζ_p(1/2+it)|², a perfect square; ∞: the
> prolate/Sonine cone of Connes–Consani). The obstruction class vanishes on every finite
> subcover: Connes–Consani's semi-local trace formula realizes each finite sum Σ_{v∈S} W_v
> operator-theoretically, and support-restricted positivity (Yoshida/Bombieri) is its
> quantitative shadow. RH is exactly the vanishing of the induced limit (lim¹-type) class.
> There is no finite-place-set witness of the obstruction and no coarse quotient that kills
> it; every recorded no-go in the corpus is a computation that the class survives one more
> localization.

The field this demands is not another route: it is the obstruction theory of positive
structures under localization-to-places — *positivity descent theory* — whose first task is to
present the limit class as a computable object and prove unconditional structure theorems
about it.

## Explanatory-completeness audit (the law must explain every recorded wall)

| Corpus wall / no-go | Reading under the law |
|---|---|
| Five lanes, one wall ("positivity must be created") | Positivity exists locally and semilocally for free; what must be created is the *limit gluing*. All five lanes work in coarse quotients where the class provably survives. |
| Criterion trichotomy; group 3 = exactly-RH | Group-3 criteria are presentations of the limit class itself; groups 1–2 are its finite-truncation shadows. The group-3 boundary = the finite/infinite resolution boundary. |
| N1 moment-blindness (proved this session) | The moment functor factors through a quotient in which every finite truncation of the class is already zero — moments cannot see a lim¹ invariant. |
| Finite-amplifier width cap δ𝔏 ≤ C(Q); Fejér ratio ρ | The quantified finite-subcover statement: any finite amplifier is a finite-place/finite-support localization; the cap measures the class's survival rate. |
| Envelope no-go; conjugation-no-sign; weld trilemma | Coarse localizations (size data, symmetry data, finite-rank data); the class survives each — recorded as no-gos, now read as nonvanishing computations. |
| Perron caps (coefficient-blind; uniform distance = prime mass) | Coefficient-blind = quotient by exactly the local data that carry the cones. |
| MR wall; zero-free-region exponent wall | Short-interval / zero-density localizations: finite-resolution windows in the same sense; the walls are the class's survival at those resolutions. |
| Rectangular terminus ("the carrier is ψ(x)−x") | The vacuum-ledger computation of ULF-FORK-1: completing each local form costs θ(e^{2R}) of vacuum mass against same-order pole compensation; the limit class *is* the ψ(x)−x cancellation, stated cone-theoretically. |
| N5 noncompact Euler corner / UV model | Why the limit does not commute: the corner is the geometric locus of the tail of places; the UV demand is the demand for a convergent presentation of the limit class. |

No recorded wall resists the reading. This passes the user's gate "explains all the theorems
and no-gos" at the explanatory level; leverage still requires the first theorem below.

## First-theorem target (make-or-die for the field)

**Descent-defect law (target, unconditional):** for tests of support radius R and any finite
place set S ⊇ {∞}:

    W_global(g ⋆ g̃*) = W_S-semilocal(g ⋆ g̃*) − D(S, R; g),

where W_S-semilocal ≥ 0 is the Connes–Consani semilocal form and the defect D(S,R;g) is an
explicit Chebyshev-type sum over primes p ∉ S with p ≤ e^{2R} — both sides unconditional
objects. Then the actual theorem to fight for: **a positivity domain for the global Weil form
strictly larger than the classical support-restricted domain** (Yoshida), cut out by an
unconditional domination of the prime-tail defect by the semilocal positivity mass.

- If the domain does not extend beyond support restriction: verdict INSIGNIFICANT — the field
  reproduces Yoshida with new words; record and refreeze from what the failure isolates.
- If it does extend: first genuinely new unconditional leverage — a new positivity region for
  the Weil form, hence new unconditional inequalities on zeros, produced *by the field* and
  not by any single route.
- Uniformity question (the field's fundamental invariant): the degradation rate κ(S, R) of
  semilocal positivity constants as S and R grow. Uniform κ would contradict the corpus caps
  or prove RH-grade statements; the corpus caps (Fejér ratio, amplifier width, dampedSize
  tail) should REAPPEAR as unconditional lower bounds on the degradation — deriving even one
  cap from the descent presentation is an acceptable first theorem (it would unify the caps,
  which the corpus proves one at a time).

## Mandatory collision pass before any proof work

1. Connes–Consani semilocal papers: exact scope of S (arbitrary finite?), exact positivity
   statement, and whether any uniformity in S is claimed — arXiv:1910.14368 (Scaling
   Hamiltonian), the semilocal-adelic-operators sequel, arXiv:2006.13771.
2. Support-restricted positivity literature: Yoshida's theorem's exact domain; Bombieri's
   quadratic-functional papers I–II; anything that already trades support restriction against
   prime-tail terms (this is the direct rediscovery risk for the descent-defect law).
3. Krein/screw-function machinery on the Weil form: arXiv:2606.09096 (*Weil's quadratic form
   via the screw function*, 2026) — positive-definite-function technology on exactly this
   form; read before claiming any cone-presentation as new.
4. Connes's 2026 survey arXiv:2602.04022 for the current state of the adele-class program.
5. Corpus: dampedSize-tail memory, finite-amplifier card, rectangular-terminus card,
   support-extraction log — the defect D(S,R;g) may partially exist in-tree.

## Falsifiers

1. The descent-defect identity fails to be exact (semilocal form ≠ global minus tail in CC's
   normalization) — the law's Čech presentation is wrong; refreeze on the corrected complex.
2. The extended positivity domain collapses to Yoshida's — INSIGNIFICANT; the limit class has
   no finite-codimension presentation and the field must attack the class itself.
3. A finite subcover already witnesses the obstruction (semilocal positivity fails for some
   finite S in the exact global normalization) — the lim¹ reading is FALSE; that failure locus
   would itself be new leverage (a finite witness of non-positivity is a computable object).
4. The screw-function paper or CC already state the descent framing — REDISCOVERED; residual
   is only the no-go-corpus audit table above.

## Discipline

No Lean until the field produces a new unconditional theorem on paper (user directive
2026-08-09). Collision pass before proof work. Verdicts recorded at every step. ULF-FORK-1 is
CLOSED; ULF-INV-10 certification remains PARKED.

## Log

- 2026-08-09 — chartered from FORK-1's death. Explanatory-completeness audit passed against
  the full wall table. First-theorem target and its INSIGNIFICANT-branch falsifier named
  before any construction.
