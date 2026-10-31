# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route), `walls-ledger.md` (walls) and
`route-unification-ledger.md` (core problems). Item labels `A*`, `B*`, `S*` refer to
`route-obstacles.md`; wall labels to `walls-ledger.md`. `[L]` = Lean anchor read.

## Picture in five lines

1. All routes read one integer, the index `κ` of Weil's correlation on the dilations of `Aff(ℚ)`; RH
   is `κ = 0`. Sign (Σ), count (Π) and selection (Γ) are three readings of `κ`.
2. Estimates reach a quantified ceiling: on the complete Weil matrix every residual saves only powers
   of `log N`, and the floor decays like `c⁻⁷`; positivity is proved up to overlap `(log N)^{1/19}` on
   fixed packets, RH needs `(log N)^{α>¼}` (Σ1c, Π10).
3. Every finite-index or finite-support waypoint already implies Lindelöf and a zero-free half-plane;
   every exponent gain on a count is a quasi-RH statement (Σ5, Π11).
4. The signature calculus is complete locally (one square per place, separable assemblies, finite
   sieves) and provably blind globally: twin-invariant, zero-or-infinity for Hecke-supported carriers,
   infinite for continuous archimedean dilation against height decay, and unable to tell ℤ from
   `𝔽_q[T]` (Σ9, Γ3, Γ9, Γ10).
5. What is missing is one object carrying two of the three readings at once — the role the Frobenius
   graph plays over `𝔽_q`.

## 2.1 Obstacles that are just work

Known mathematics, finite computation, effectivisation or bookkeeping. Ordered by leverage.

| # | Task | Routes served | Why it is work, not research |
|---|---|---|---|
| 1 | Effective horizon for the fixed-`c` logarithmic reserve: explicit `N₀(c)` of any size (A1) | HF, SRT, AIP, CHMD, ACS, SC | expected source of the eventuality: limits of prime sums, which have explicit error terms (a horizon `exp(c^K)` with `K < 4` is Q1, not work) |
| 2 | All-vector complete positivity at iterated-log overlap (A2) | same | combine 1 with the conductor-uniform residual for `m ≤ (log N)^A` [L] |
| 3 | Attribute the eight residual terms (prime sum vs horizon / top band) and insert de la Vallée Poussin errors in the prime-sum terms (A3) | same | bookkeeping on proven bounds; decides the exponents in Σ1c |
| 4 | Growing-packet head-pole cancellation, packets up to `exp(c√log Y)` (A4) | CHMD, HF, AIP | window PNT with classical error, summed over growing families |
| 5 | Single-`K` completeness of the Steklov/sinc schedule at `K L(log L)²` (A5) | SRT, HF | synthesis error at a fixed explicit scale |
| 6 | Explicit capture stage for complete-cell indices (A6) | AID, HF, CHMD | effectivise an existing compactness transfer |
| 7 | Formalise a stronger subconvexity exponent to lower the heat floor `2/3 = 4μ(½)` (A7) | WD, LA | known exponent; calibration of the heat horizon only |
| 8 | Effective rounding of theta-prefix collision readings on a fixed window (A8) | WD, TG, HF | explicit Gaussian tail errors |
| 9 | Univariate integer-Chebyshev ceiling (A9) | WL | classical; fixes the ceiling of single-variable auxiliaries |
| 10 | Same-order mixed-jet recovery for `≥ 3` primes (A10) | WL, ACS | algebra of Dirichlet jets |
| 11 | `XiZeroCopy`-free PW-B theta instantiation where it is notational (A11) | PW-B | rewriting |
| 12 | F₃ automorphic chain: unipotent quotient measure, Eisenstein series on the restricted elliptic loop group, absolute convergence, constant term | ACS | function-field loop-group theory |
| 13 | Certified Weil positivity past the two-prime aperture (`r ≥ ½ log 3`), odd and full | RW, EWU, OWU, CHMD | finite-aperture problem; prolate / certified numerics |
| 14 | Theta Hankel rank-8 strictness, ranks 9 and 10 | TH | finite computations |
| 15 | Explicit thresholds: Hausdorff shifts per order (PA), Jensen degree horizons (LA), fixed-degree two-grid checks (HCF) | PA, LA, HCF | effectivise eventual statements |
| 16 | The nine atom-dominated moduli of the collar shift | ACT | finite case analysis |
| 17 | Mixed Schur debit on fixed blocks; first-prime / coarse / polar costs on fixed cells | AIP, CHMD | fixed-dimensional estimates |

## 2.2 Open mathematical obstacles

Strength: **RH** equivalent to RH; **≥qRH** implies Lindelöf and a zero-free half-plane; **sub**
strictly weaker or unknown.

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| Σ-1 | Complete Weil positivity on an RH-complete schedule (B1) | RH | HF, SRT, AIP, ACT, ACS, SC, RW, EWU, OWU |
| Σ-2 | Which link of the complete-Weil chain carries RH: horizon exponent `K < 4` or residual saving `b > (a+14)/4` (B2) | open which; one is ≥ RH-hard | same |
| Σ-3 | Odd-sector bound `R ≤ ½` / positive supersolution at the half threshold | RH | CHMD, TT |
| Σ-4 | All-rank / all-degree sign of theta, heat and Jensen Hankels | RH | TH, LA, HCF, PA, GTA |
| Σ-5 | An arithmetic index ceiling uniform in resolution (B4) | ≥qRH | CHMD, SRT, WD, AID |
| Σ-6 | Heat count `N(t) ≤ exp(At^{−a})`, `a < 1` (B6) | sub (beyond the density hypothesis) | WD |
| Σ-7 | Source-side collision charge `< 2` on every window (B8) | RH | WD, TG |
| Σ-8 | Lower bounds for scheduled prime energies (FU, CFC, RP, SZ, LI, FEL) | RH | scheduled-sum face |
| Σ-9 | Spectral reality of a realized operator: renewal, photonic port, Lee–Yang couplings | RH | RN, PTR, W1C, PM |
| Σ-10 | Infinite assembly with a running counterterm (Σ10) | RH | SC, AKG, HF |
| Σ-11 | Joint positivity of non-arithmetic Gamma graph + signed diagonal + prime reserve + poles | Σ-strength unknown | CHMD, AID |

### Π — square-root precision
| # | Problem | Strength | Routes |
|---|---|---|---|
| Π-1 | Unconditional one-sided count at square-root precision (B10) | RH | WL, PBM, RB, JAS, CTF |
| Π-2 | Moving-scale half-power Möbius cancellation; near-band cyclotomic energy `O(N^{3/2+ε})` | RH; ≥qRH | MC |
| Π-3 | Parity-selective integer auxiliaries beyond the Landau class (B11) | sub | WL |
| Π-4 | Characteristic-0 quadratic effectivity on the scaling surface (B12) | RH | ACS |
| Π-5 | Conductor uniformity beyond `(log x)^A` (B3) | sub | HF, MC, CACT |
| Π-6 | Breaking the logarithmic-saving barrier for any sign-relevant residual (Π10) | sub | complete-Weil cluster |
| Π-7 | 100% census; census displacement survives projection | sub | ACS, SRT, IGP |
| Π-8 | Theta-prefix rounding uniform in height (B9) | sub | WD |

### Γ — selection
| # | Problem | Strength | Routes |
|---|---|---|---|
| Γ-1 | Zero-independent selection at the trivial gauge point (B14) | RH | MC, BAG, XN, PM, PW-B |
| Γ-2 | Finite-index `Aff(ℚ)` states with continuous dilation reading: classification (B13) | sub | SC, AKG, APD |
| Γ-3 | Hecke invariance of the collided form | RH | AP, CDG |
| Γ-4 | Pre-divisor sections / potentials coupled to Ξ (BSH, CDC, HJ, SEC, PCS, RFHM, DR, EWJ, APF, WBF) | RH | Γ-candidates |
| Γ-5 | A conformal correspondence over ℤ whose factor is not archimedean size, with bounded self-intersection | RH | ACS, ALG |

## 2.3 The three questions to answer next

**Q1. Where does the RH content sit in the complete-Weil chain?**
The chain is: reserve (negative vectors have small defect) → approximation (small defect ⇒ low
conductors) → quasimodes (low conductors have positive completed energy with small residual). Every
link is a theorem at fixed `c`; at `c = (log N)^α` the reach is `α < b/(a+14)` from the residual
exponents, and the log reserve's horizon is ineffective in `c`. Under ¬RH, at `α > ¼`, some link must
fail. Determine which: (i) an effective horizon `N ≥ exp(c^K)` with `K < 4`, or (ii) a residual
saving `b > (a+14)/4` on the dominant term. If the dominant residual term is a horizon/top-band term
with a matching lower bound, the cluster HF/SRT/AIP/CHMD/ACS-atomic/SC has a proved ceiling below RH;
if it is a prime-sum term (improvable by classical error terms), the RH content sits in the horizon
effectivity of the logarithmic reserve — an effectivity statement, not a precision statement. Either
answer re-plans the largest route cluster. Starting
points: A1, A3; CACT `CompleteConductorResidualsAreUniformOnLogarithmicFamilies`,
`ShiftingThePrimeEnergyGivesALogarithmicDefectReserve`.

**Q2. Are all finite-index Hermitian states on `Aff(ℚ)` with dilation reading continuous at `1`
pulled back from the slope?**
Known [L]: Hecke-supported, separable and integer-successor carriers with continuous dilation have
`κ = ∞`; finite-dimensional unitary representations factor through the slope; finite column rank
forces polynomial translation fibres; kernels vanishing on both axes have `κ = 0` or `≥ 2`. A
classification theorem would close the carrier question on `Aff(ℚ)`: either every finite-index state
with continuous (Weil-type) dilation is translation-blind — then a selecting carrier must live on a
larger group (`Aff(𝔸)`, the loop groups of ACS), and SC/AKG/APD hand over to the automorphic branch
— or an exceptional state exists, which is the first candidate carrier with Weil dilation, visible
successor and finite index. The question is strictly weaker than RH and is pure harmonic analysis on
`Aff(ℚ)`.

**Q3. Does the complete Weil residual admit a level of distribution?**
Prove a mean-value bound `Σ_{m ≤ N^θ} ‖(W − E_m(c))v_m‖² ≤ (small) · Σ_m E_m(c)²` for some `θ > 0` at
overlap on an RH-complete schedule — the Bombieri–Vinogradov analogue for the complete Weil matrix. By
min–max, the negative index is then bounded by the number of exceptional conductors plus the
high-defect complement (controlled by the reserve), giving `κ(W_N) = o(#modes)`: the first sign
statement at RH-complete resolution. Large-sieve and dispersion tools apply to averages, not to
individual conductors, so this question moves part of Σ-1 into the regime where unconditional
mathematics works. No averaged residual statement exists in the corpus.

## 2.4 A wildly different route

**The weight route (tensor-power amplification over a family).** Over `𝔽_q`, Deligne's proof of
purity uses neither a critical sign nor square-root precision. It needs (i) a crude bound
`|α| ≤ q^{w/2 + 1/2}` with a loss independent of the weight `w`, obtained from nonnegative-coefficient
(Rankin-square) L-functions and their first real pole (Landau); (ii) tensor powers: applied to the
`k`-th tensor power, of weight `kw`, the same fixed loss gives `|α|^k ≤ q^{kw/2 + 1/2}`, so the loss
disappears as `k → ∞`; (iii) a family (a lisse sheaf on a curve), so that tensor powers are again
arithmetic objects with Euler products, with big monodromy controlling their top cohomology.

Over ℤ the route reads: build arithmetic objects `Z_k` whose spectrum contains `ρ₁ + … + ρ_k` (the
`k`-th tensor power of the zeros), with an Euler product, and prove for them a crude zero-free bound
`Re ≤ k/2 + C` with `C` independent of `k`. Then `k Re ρ ≤ k/2 + C` for every `k` gives `Re ρ ≤ ½`.

Why it avoids the three walls:
- **Σ**: the only positivity used is nonnegativity of Dirichlet coefficients of a Rankin square and
  Landau's theorem — trivially true and far from the critical sign; the corpus already holds the
  sign-free mechanisms (`ZetaMultipleLandauZeroFree`, `FiniteOffLineLandau` [L]) and the abstract
  inertia version (bounded negative index over all tensor degrees ⇔ positivity,
  `TensorPolarizationAmplification` [L]).
- **Π**: no estimate needs square-root precision; any fixed loss is amplified away. The killed route
  "no extra exponent at fixed total support" does not apply, because the weight grows with `k` while
  the loss stays fixed.
- **Γ**: weights select. The Liouville twin `ζ(2s)/ζ(s)` is mixed (zeros from `ζ(2s)`, poles from
  `ζ(s)`); a weight formalism rejects it structurally, and Davenport–Heilbronn combinations have no
  Euler product to tensor.

The wall it faces instead is a **realization wall**: the arithmetic tensor powers. Over `𝔽_q` they are
the cohomology of `C^k` and their L-functions are point counts on `C^k`. Over ℤ the analogue is the
scaling surface `Spec ℤ × Spec ℤ` and its powers (ACS) with a Künneth formula whose H² carries
`ρ + ρ'`; the zeta-regularized "tensor products" built from the zeros exist analytically but have no
known Euler product. The corpus has neither tensor powers of the Weil form nor a Künneth statement
beyond point-count positivity. The route is far from every live route: no positivity on a test cone,
no count, no gauge selection — only a crude bound, an amplification and an existence question.

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — positivity on average
**Question.** Is the complete Weil form nonnegative *on average over conductors* at RH-complete
resolution: does a level of distribution `θ > 0` hold for the complete residuals (Q3), so that
`κ(W_N) = o(#conductor modes)`?
- **Below RH / quasi-RH**: an averaged statement allows infinitely many off-line zeros of any depth,
  as Bombieri–Vinogradov allows GRH failures.
- **Advance**: the first sign information on the complete source at the resolution where positivity is
  RH; converts Σ-1 into an averaged Π-problem where large-sieve technology works; an index bound
  `o(#modes)` reads as a census statement produced by positivity, linking the U-Σ cluster with the
  census face.

### 2.5.2 Route WD — an integer realization of the collision charge
**Question.** Construct from integers alone (theta prefixes, primes, Gamma) a Fredholm operator or a
winding number on each natural-height window whose index equals the horizontal collision charge `O`.
First milestone: an explicit rate for the theta-prefix readings to round to `O` on a fixed window (A8),
then uniformly in height.
- **Below RH / quasi-RH**: an identity between an index and `O`; it says nothing about `O`'s value.
- **Advance**: WD's remaining obstacle is a source-side bound `O < 2`. With an index realization the
  required precision is integrality (error `< 1`), not square-root precision, and homotopy invariance
  becomes available: the heat flow itself is a homotopy along which an index can change only when a
  zero crosses the window boundary. It joins WD with APF and IRK, which lack exactly such an integral
  source count.

### 2.5.3 Route ACS — RH for `y² = x³ − x` over `𝔽₃` through the loop Eisenstein series
**Question.** On the restricted central loop group of the elliptic curve over `𝔽₃` (built [L]),
compute the constant term of the loop Eisenstein series and show that its convergence and positivity
force the Weil bound `|α| = √3`, without Frobenius acting on cohomology.
- **Below RH**: RH for this curve is a theorem; the question asks for a new proof by the automorphic
  ACS mechanism.
- **Advance**: decides whether the automorphic branch is a producer or only a receiver. A positive
  answer isolates the exact step where the finite field's quantized conformal factor enters (Γ10) and
  gives the template the characteristic-0 loop group must follow; a negative answer retires the
  automorphic branch with a precise obstruction. All objects up to the Eisenstein series are in the
  corpus; the constant term is the first missing one.

### 2.5.4 Route WL — a parity-selective producer at the main term
**Question.** Do multivariate, parity-selective integer auxiliaries (outside the Hecke algebra of a
single prime) yield the prime number theorem upper bound `ψ(x) ≤ (1 + ε)x` by vanishing-order
arguments alone, beating the univariate integer-Chebyshev ceiling (A9)?
- **Below RH / quasi-RH**: PNT is known; the question concerns the mechanism and keeps the exponent at
  `1`, so it is not a quasi-RH statement (Π11).
- **Advance**: WL's producer branch currently stops at Chebyshev strength (`ψ ≥ 0.89x`) and at the
  Landau factorial cost. Reaching the main term would be the first evidence that integer auxiliaries
  with parity selection carry information beyond the classical integer-Chebyshev barrier — the
  `ℤ`-analogue of the step where Stepanov's auxiliary beats the trivial count. A proof that they cannot
  would close the producer branch and leave WL a receiver.

### 2.5.5 Route CHMD — the odd-sector ground state at the two-prime aperture
**Question.** Prove nonnegative Doob energy — equivalently `⟨Rw, w⟩ ≤ ½‖w‖²` — for every odd compact
test supported in `[−r, r]` with `r = 0.55` (so that `log 2` and `log 3` both enter, `2r > log 3`),
using the CHMD Doob/nodal decomposition and the Gamma-graph payment of the prime-two and prime-three
blocks.
- **Below RH**: fixed aperture is never RH-complete.
- **Advance**: for every `r > 27/50` one odd test has `W_ζ > mass/25` and `W_Liouville < −3 mass/10`
  (OWU, frontier map); positivity on *all* odd tests at `r = 0.55` would be the first theorem in which
  a full test space is both positive for ζ and selective against the twin, with two interacting prime
  atoms paid by the non-arithmetic Gamma graph — the joint payment CHMD lacks (Σ-11), at the smallest
  scale where it is nontrivial. The proved floors stop below `½`.

## 2.6 Does closing RH need a new field?

**Assessment: yes.** Each existing language is provably insufficient on its own:
- *Estimates* stop at overlap `(log N)^{1/19}` while RH needs `(log N)^{α>¼}`; every count-side
  exponent gain is quasi-RH (Σ1c, Π10, Π11).
- *Index calculus* is local-complete and global-blind: twin-invariant, zero-or-infinity for supported
  carriers, infinite for continuous archimedean dilation against height decay, indifferent between ℤ
  and `𝔽_q[T]` (Γ3, Γ9, Γ10); and any finite index is already ≥qRH (Σ5).
- *Effectivity geometry* has an exact linear Riemann–Roch for the base and no quadratic one for the
  surface (Π-4).
- *Heat and realization* convert the sign into an equally hard reality statement (Σ5, Σ6, Σ8).

The signature theory required by Σ9 and Γ7 exists as adelic Krein geometry; its theorems
locate the gap precisely: per place the pole costs one square and positivity off the pole is an
identity, but the infinite assembly needs a counterterm that runs with the cutoff, and selection must
come from dilation data. The missing field is the geometry in which that running counterterm is
canonical and the archimedean dilation acts like a Frobenius.

**Working name: renormalized intersection theory of the scaling surface.**

*What it is about.* Intersection theory on `Spec ℤ × Spec ℤ` (the scaling surface) where the
Frobenius graph of `C × C` is replaced by the continuous family of scaling correspondences `Γ_u`,
`u ∈ ℝ_{>0}`, whose intersection numbers with the diagonal are the explicit formula and whose
self-intersections diverge and must be renormalized by a running counterterm (`log N − γ`).

*What it would be like.* Arakelov geometry with a continuous Frobenius: local terms are
shell decompositions (sums of squares over agreement shells at finite places, dyadic Haar cells at the
real place), global terms are renormalized pairings, and the central theorem is a renormalized Hodge
index theorem.

*Criteria it must meet.*
1. Calibration: over `𝔽_q` it reproduces Weil's RH with the quantized factor `q`; on the golden datum
   it fails where the Hodge index fails.
2. Positivity by identity: the sign of the renormalized pairing comes from a sum-of-squares identity
   uniform in the cutoff, not from estimates.
3. Quadratic Riemann–Roch: a sign-free `h⁰` on the scaling surface with Hilbert–Samuel growth (not a
   function of the degree alone).
4. Canonical renormalization: counterterms run with the cutoff and their finite parts are intrinsic
   (as `γ` in `log N − γ`); index statements pass to the renormalized limit.
5. One topology for both readings: the archimedean dilation reading and the finite-adelic height decay
   are simultaneously continuous (removing Γ9).
6. Integrality: intersection numbers and indices are integers, so precision `< 1` suffices (Σ8).
7. Zero-independence and twin sensitivity: built from integers and adeles only, and reading the pole
   and Gamma data that separate ζ from its twins.

*Questions it must answer.*
- What is the renormalized self-intersection `Γ_u · Γ_u`, and does a Castelnuovo–Severi inequality hold
  for it?
- On the orthogonal complement of the hyperbolic pole–successor plane, is the renormalized pairing
  definite (renormalized Hodge index)?
- What is `h⁰` on the scaling surface, and what is its Serre dual?
- Which finite-index states on `Aff(ℚ)` or `Aff(𝔸)` carry Weil's dilation (Q2)?
- Is the collision quantum `O` an intersection number?
- Is there a Künneth formula whose H² carries `ρ + ρ'` with an Euler product (the weight route, 2.4)?

*Tools it aims to develop.* Renormalized Pontryagin spaces with running counterterms; adelic shell
decompositions with an archimedean shell calculus; index theorems for renormalized Toeplitz/Fredholm
forms; theta log-volumes as `h⁰`; loop-group Eisenstein series over ℚ as global carriers; the heat flow
as a homotopy preserving renormalized indices.

*Objects, language, mechanisms.* The adele class space and the scaling surface; the correspondences
`Γ_u`; pole–successor hyperbolic planes and conformal successors; agreement shells; renormalized
pairings and counterterms; collided and Weil forms as the positive and the equivariant reading of one
pairing; collision quanta; tensor powers of `H¹(Spec ℤ)`.
