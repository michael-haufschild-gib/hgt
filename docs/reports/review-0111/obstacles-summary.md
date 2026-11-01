# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route), `walls-ledger.md` (walls) and
`route-unification-ledger.md` (core problems and route classes). Labels `A*`, `B*`, `S*` refer to
`route-obstacles.md`; wall labels to `walls-ledger.md`. Corpus: `6e0189d741` and the working tree.

Evidence:
- `[L]` Lean statement or module docstring read.
- `[U]` Lean file unfinished or not yet integrated.
- `[M]` frontier-map or killed-routes entry, Lean not re-read.
- `[D]` derived here, not formalized.

## Picture

1. **One even integer, one hyperplane, one Kähler package.** Every route reads `κ = #` distinct
   zeros right of the line [M]. Glued at any place it is `κ + 1` [L]. It is the Hodge defect on
   `v₁^⊥` and the number of zeros moved by `σ(ρ) = 1 − ρ̄` [L]. `κ` is even, and RH is `κ < 2`
   [L]. HWV makes `(W_{c,N}, v₁)` a formal Kähler package [L]: Hodge–Riemann (HR) transports along
   the overlap flow wherever hard Lefschetz (HL) holds on the HR locus, and losing HR forces a
   primitive zero mode. RH ⇔ HL on the positive locus along `1 ≤ c ≤ 2(log N)^β`, `β > ½` [U].
   Deformation costs nothing; every deformation argument has nondegeneracy as its whole content.
2. **The overlap axis is the aperture axis** (receiver theory, [L]).
   - For Denjoy–Carleman and sinc profiles the critical overlap `c*_N ≍ L(log L)²`,
     `L = loglog N`, is where margin = synthesis error = `1/log N`.
   - RH ⇔ positivity at every multiple `K·c*_N`; the multiple `K` sees every smooth test of radius
     `½ log K + O(1)`.
   - The tilted spline is proved positive on all vectors to `(log N)^{1/16}` [L]; its receiver
     starts at `α > ¼` [L].
   - No corpus receiver turns positivity below the receiver threshold into a statement about
     zeros. Whether vectors that depend on `N` can see zeros there is open.
3. **The aperture floor dies doubly exponentially** [L]. Unconditionally
   `μ(A) ≤ K exp((11/2)A − πe^{2(A−2)})` for `A ≥ 3`. No positive floor holds along any unbounded
   aperture sequence, and every positive aperture transport must lose at a doubly exponential rate.
   - So no producer with polynomial or exponential loss reaches all apertures.
   - A producer must be exact (an identity), quantized (an integer read below `2`), or structural
     (a selection that forces sign).
   - In the RVM model an isolated pair is seen at aperture `a` iff
     `S_δ(a) = sinh(2δa)/(2δ) − a > (1/2π)log(ξ/2π)` [L].
4. **The rough regime of the tilted spline.** Proved [L]: all vectors `α < 1/16`; complement of
   polynomial conductors `α < 1/9`; confinement `log R' ≤ Cc¹¹`. In progress [U]: packets
   `α < 1/8`. The binding term is the quadratic single-conductor residual against floor²
   (`c¹⁶/log N`). These exponents describe the profile below its receiver threshold.
5. **Kernel, coupling and window error are one quantity.** RH ⇔ bounded `K_ζ` [L]; one lattice
   `⟨p⟩ × ⟨q⟩` decides; rate = width [L]. `K_ζ(u)` is the normalized smoothed prime error in a
   multiplicative window [D].
6. **The exact pieces of the complete form.**
   - The packet identity: jump squares + affine incidence squares + bounded diagonal − shell degree
     + boundary [M].
   - The matched prime form has exactly one positive direction on every finite sieve, at one
     horizon independent of the sieve [L].
   - The shell degree is the only overlap-growing non-square term [M].
   So the prime part has a uniform Lorentzian signature, and growth comes from the additive
   (successor) coupling.
7. **Stars.**
   - The star of `d` is the complete family at `(c⌊N/d⌋/N, ⌊N/d⌋)`, isometric for every weight
     [L].
   - Positivity descends to stars, and deep stars are positive [L].
   - Only the counterterm selects: its flux `log d` is self-similar exactly for generalized von
     Mangoldt weights [L].
   - There is no mechanism for ascent. The gcd/Möbius decomposition of a form into star pieces
     holds for every symmetric matrix on ℕ and carries no arithmetic [D].
8. **Riemann–Roch is the producer the corpus has identified.**
   - The scaling surface has cycles `aH + bV + f` (`f` a test). Its pairing is
     `f·g = B(f)A(g) + A(f)B(g) − Re W(f,g)`, and its Castelnuovo–Severi defect is Weil's form
     [L].
   - RH ⇔ there exists an effectivity with the Riemann–Roch and ample axioms. Positivity-defined
     cones fail the Riemann–Roch axiom unconditionally [L].
   - Quadratic RR with a Serre-dual `h⁰` ⇔ renormalized Hodge index ⇔ RH [L].
   - The theta `h⁰` of van der Geer–Schoof gives RR on `Spec ℤ` and on the pole plane by Poisson
     summation, with `h⁰ > 0` by construction [L].
   - The corpus records the missing piece in so many words: "Riemann–Roch on the surface, for
     classes with a test component" [L].
   - Naive constructions are refuted [L/M]: finite readings, positive counts, determinant data,
     Boolean sections, positive majorants; the polar box minus `ψ`; exact source effectivity needs
     infinitely many degrees.
9. **Quantization.** RH is `κ < 2` and `O(T) < 2` per window, with `O ∈ 2ℕ` [L].
   - Integer-theta Fredholm indices read the collision charge; a source-intrinsic stopping rule is
     sound and eventually complete [L].
   - The first stabilized prefix is unbounded in height. The certificate depends on window-boundary
     moduli of finite theta amplitudes and on scales tied to divisor separation [L].
   - Quantization is the only mechanism in the corpus that turns `O(1)`-precision information into
     an exact statement.
10. **The first rung.** Finite Hodge defect ⇔ bounded heat counts ⇔ bounded collision charges ⇔ all
    zeros above some height critical [L]. It gives `Θ < 1` and power savings in short windows: RH
    with finitely many exceptions [L].
    - On that stratum one nonblind prime tower decides RH [M], and so does single-lattice coupling
      [L].
11. **Unattained width recurs.** It is the alternative left by the cone theorem [L], by tower
    detection [L] and by PM's escape tightness [M]. Attainment of `Θ = sup Re ρ` implies `Θ < 1`,
    because `ζ` has no zeros on `Re s = 1` [D]. Excluding the unattained case unconditionally is
    therefore at least qRH; only the pure implication "bounded cone coupling ⇒ RH" is sub.
12. **The Hecke defect has an exact hierarchy** [L].
    - Dyadic means: `O_c(log U)` for `c < 22/51`; `o(log U)` ⇔ 100% critical-scale clustering.
    - Fixed scale: `O(1)` ⇔ corridor (≥qRH). All scales: one constant over dyadic scales ⇔ RH.
    - Counts + linear explicit formula cannot bound it.
    - Every pointwise step is at least qRH: a bound `E_γ(c log T) ≤ T^η` forces depth `≤ η/(2c)`
      [D].
13. **Frobenius at infinity has four RH-equivalent readings** [L]: `σ` trivial on the zeros; Hecke
    similitude of the collided form; one constant for the dyadic Hecke defects; partner saturation
    of resonant Eisenstein states (`cos² = 4Reρ(1 − Reρ)`).
14. **Selection among prime flips is closed; selectors do not produce sign** [L/M].
15. **Finite index has a constraint classification** [L]: `κ ≤ r` iff translation-stable positive
    constraints of dimension `≤ r` exist.
16. **PM has a constructed determinant** [L]: the regularized Gauss–Mayer Fredholm determinant
    `D(w,λ) = A + ζ(w)B`, with `B(w,−1) = 0`. Algebraic recentering of the critical parabola is
    impossible [L].
17. **Census and growth.** Simple critical zeros `≥ 0.67250071` [L]; `ζ(5/6+it) ≪ t^{2/53} log t`
    [L]; `μ(½) ≤ 33/200` [U].
    - The heat floor `2/3` is set by three pieces of the Ki–Kim–Lee strip profile. The `w ≥ 3/14`
      piece is certified only for `c > 2/3` [L], so `μ(½) ≤ 33/200` alone does not lower it.
18. **Reformulations do not soften; falsification certificates have no converse** [L/M].

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Fourth-order synthesis for the tilted spline (receiver at `K(log N)^{1/8}`, every `K`) | HF, SRT, AIP, ACS | [Formalized](../../drafts/pipeline/3-formalized/tilted-spline-fourth-order-synthesis.md): full-space and pole-hyperplane endpoint receivers |
| A2 | Bilinear conductor-residual theorem: packets and polylog subspaces for `α < 1/8` | HF, SRT, AIP, ACS | [Formalized](../../drafts/pipeline/3-formalized/one-eighth-conductor-packet-positivity.md): fixed packets; polylog subspaces when `α + 2q < 1` |
| A3 | Rough regime for a tilted Denjoy–Carleman profile up to `ε·c*_N` (sinc itself has real Fourier zeros) | HF, SRT, AIP, ACS | profile constants; existence of tilts without real zeros proved |
| A4 | Edge of one off-line pair at atomic resolution in the RVM model | HF, SRT, RW, EHT | composition of the visibility law with the `K ↔ ½ log K` transfer |
| A5 | Propagate `1/16` into the EHT edge-window and crossing theorems (Lean: `1/59`) | EHT, HF, SRT, SC | composition |
| A6 | Explicit horizon `N₀` for the `1/16` theorem | HF, SRT, AIP, ACS | constants |
| A7 | Single-`K` completeness of the Steklov/sinc schedule | SRT, HF | one explicit scale |
| A8 | Size of the shell degree `d_n` at overlap `c` | HF, AIP, SRT, ACS | explicit sums |
| A9 | CSAR rigidity vs complete energy on fixed and slowly growing packets | HF, SRT, AIP, ACS | packet identity |
| A10 | Rate for the smooth no-real-zero tilt profile | HF, SRT, EHT | rerun |
| A11 | Critical-scale identification of smooth-bump packets with ratCorr Grams | SC, HF, ACS | synthesis + Lévy continuity |
| A12 | Certified Weil positivity past `½ log 3` (two primes) | RW, EWU, OWU, CHMD, HF | certified numerics; the doubly exponential ceiling only bites from `A ≈ 3` |
| A13 | Quantitative star range | HF, ACS | effectivize `exists_star_positive_tiltedUnitSpline` |
| A14 | Re-derive the Ki–Kim–Lee threshold with `μ(½) ≤ 33/200`: which of the three strip pieces binds | WD, LA | existing machinery; the `w ≥ 3/14` piece is certified only for `c > 2/3` |
| A15 | Certified de Bruijn–Newman upper bound as an index-one heat time | SC-heat, WD | certified numerics |
| A16 | One Lean statement: `ΔO = o(log T)` ⇒ off-line sparsity ⇒ Lindelöf | WD, SRT | composition |
| A17 | Computable stopping prefix (interval bounds) | WD | interval arithmetic |
| A18 | Same-order mixed-jet recovery for `≥ 3` primes | WL, ACS | Dirichlet-jet algebra |
| A19 | Explicit `ε ↦ (support, coefficients, C_ε)` for the main-term producer | WL | Farkas / rounding |
| A20 | Cosine prime Gram certificate; stabilizer calibration `β = 2` | census, ACS | file in progress |
| A21 | `𝔽_q(X)` calibration: higher-degree local walls, Hecke product formula, archimedean state of a curve | SC, ACS, RIT | curve coupling and curve edge proved |
| A22 | `𝔽₃` loop chain: unfolding, Eisenstein convergence, constant term | ACS | loop-group foundations |
| A23 | Mayer determinant: general-`λ` finite part; primitive-geodesic coding; Mayer–Selberg identity; scattering link, read as "zeros of `D(·,±1)` in `½ < Re w < 1` ↔ off-line ζ zeros" | PM | known mathematics, heavy formalization |
| A24 | Theta Hankel rank-8 strictness, ranks 9 and 10 | TH | finite computations |
| A25 | Explicit thresholds: Hausdorff shifts, Jensen degree horizons, two-grid fixed degrees | PA, LA, HCF | effectivization |
| A26 | The nine atom-dominated moduli of the collar shift | ACT | finite case analysis |
| A27 | Mixed Schur debit on fixed blocks; first-prime / coarse / polar costs on fixed cells | AIP, CHMD | fixed-dimensional estimates |
| A28 | Toeplitz minors of the Xi centre sequence beyond PF₃₇ | LA | certified computation |

## 2.2 Open mathematical obstacles

Strength: **RH**; **≥qRH** (Lindelöf + zero-free half-plane); **LH**; **sub**; **indep.** (logically
independent of RH).

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Positivity at every multiple `K·c*_φ` (all-aperture Weil positivity; no zero mode on `v₁^⊥`) | RH | HF, SRT, AIP, ACT, ACS, SC, RW, EWU, OWU, CHMD |
| B2 | Joint shell–pole payment on all vectors (confinement exponent `≤ 8`) | sub | HF, SRT, AIP, ACS |
| B3 | Low-conductor spans below `(log N)^A` | sub | HF, SRT, AIP, ACS |
| B4 | Conductors `N^{½} < m ≤ N` | sub | HF, SRT, AIP, SC |
| B5 | Non-arithmetic Gamma graph + signed diagonal + roots + poles on growing packets | sub | CHMD, AID, HF |
| B7 | Exact sum-of-squares identity for the dilation form on one two-prime lattice | RH | HF, SC, ACS, RIT |
| B8 | HL on the positive locus (source-defined noncrossing) | RH | HF, TG, SC, WD |
| B9 | Star ascent: positivity of all proper stars ⇒ HL at the top (no arithmetic mechanism known) | RH | HF, ACS |
| B10 | Emptiness of the loop-Eisenstein band poles | RH | HF, ACS, SC |
| B11 | Arithmetic index ceiling uniform in resolution | ≥qRH; RH (Künneth) | CHMD, SRT, WD, AID, SC |
| B12–B16 | Heat count `a < 1` (sub); heat horizon `< ½` (≥qRH); charge `< 2` (RH); `O(T) = o(N(T))` (sub); `ΔO = o(log T)` (LH) | — | WD, LA, TG, SC-heat, census |
| B35 | Source-faithful realization (PTR, W1C, RN) | RH | RN, PTR, W1C |
| B36 | Odd-sector bound `R ≤ ½` | RH | CHMD, TT |
| B37 | All-rank / all-degree signs | RH | TH, LA, HCF, PA, GTA |
| B38 | Lower bounds for scheduled prime energies | RH | FU, CFC, RP, SZ, LI, FEL, EGC |

### Π — precision
| # | Problem | Strength | Routes |
|---|---|---|---|
| B6 | Signed cancellation of the overlap residual at `K·c*_φ` | RH (all `K`) | HF, SRT, AIP, ACS |
| B17–B22 | Gap-independent detection (sub); doubly-log Hecke defect (sub); mean `o(log U)` ⇔ critical-scale clustering (sub); fixed-scale `E = O(1)` (≥qRH); one constant over dyadic scales (RH); an input beyond counts + linear explicit formula (method) | — | WD, census, HEF |
| B23 | `ε`-uniform producer | sub / RH | WL |
| B24 | Any unconditional square-root source input | RH | WL, MC, PBM, RB, JAS, CTF |
| B26 | Near-band cyclotomic energy `O(N^{3/2+ε})` | ≥qRH | MC |
| B27 | Signed prime surplus `≤ (1/18 + o(1))N` at bandwidth `4/3` | sub | census, ACS |
| B28 | Bounded coupling on one two-prime lattice | RH | SC, ACS |
| B29 | "Bounded cone coupling ⇒ RH" (pure implication; excluding unattained width outright implies `Θ < 1`) | sub | SC, ACS |
| B34 | Zero-free region near `Re s = 1` from a Hermitian structure on the regularized Mayer operator | sub | PM |
| B40 | Height-uniform quantized reading: boundary-modulus / ordinate-separation lower bounds that make the integer-theta collision index stabilize at a prefix polynomial in height | indep. | WD, TG, SC |

### Γ — selection and geometric production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B25 | An effectivity on the scaling surface with the Riemann–Roch and ample axioms (equivalently a Serre-dual `h⁰` with quadratic RR) | RH | ACS, HF, RIT |
| B39 | An arithmetic effectivity (lattice-count `h⁰`, Poisson Serre duality) on prime-free cycles `aH + bV + f`, `supp f ⊂ (−½ log 2, ½ log 2)` | sub | ACS, HF |
| B30 | Zero-independent selection at the trivial gauge point | RH | MC, BAG, XN |
| B31 | Frobenius at infinity as an operator | RH | HF, ACS, PL, CDG, EHT |
| B32 | Unimodular gauges with `S_N/H_N → 1`; FE twins; zero-density flip twins | sub | HF, ACS, AIP, SRT, SC |
| B33 | Off-line resonance exclusion (zero-selecting scattering rigidity) | RH | PM |
| B41 | Zero–one law `κ ∈ {0, ∞}` (with the first rung it gives RH) | sub | SC, HF, ACS, SRT |
| Γ5 | Pre-divisor sections / potentials coupled to Ξ | RH | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |

## 2.3 The three questions to answer next

The corpus has proved some hundred equivalent forms of RH and a ladder of partial results. Its
frontier map names what is missing: one actual arithmetic estimate at RH strength. The doubly
exponential aperture ceiling (Picture 3) shows that an estimate with any polynomial or exponential
loss cannot be it. Two producer types escape that ceiling: exact production by Riemann–Roch, and
`O(1)`-precision production by quantization. The three questions test these two types.

**Q1. Does the scaling surface carry an arithmetic effectivity on its prime-free cycles?** Construct
an `h⁰` on cycles `aH + bV + f` with `supp f ⊂ (−½ log 2, ½ log 2)`, as the logarithm of a weighted
lattice-point count. Require:
- `h⁰ > 0` by construction;
- Serre duality by a Poisson summation;
- the Riemann–Roch and ample axioms of the polar surface on this subspace.

What is in hand:
- the scaling surface and its effectivity criterion; the refutation of positivity-defined cones
  [L];
- the theta `h⁰` with RR on `Spec ℤ` and on the pole plane, and `Λ(s)` as its Mellin generating
  function [L];
- prime-free Weil positivity, already proved by estimates (Weil floors through `181/500` cover it)
  [M/L].

Why first:
- It is the producer of Weil's proof over `𝔽_q` (RR on `C × C` ⇒ Hodge index ⇒
  Castelnuovo–Severi). The corpus has reduced RH to it exactly and isolated the missing piece:
  classes with a test component.
- RR is an identity and `h⁰ ≥ 0` is free, so the doubly exponential ceiling does not apply.
- The prime-free window is where the answer must be yes if the architecture exists. A construction
  there shows how the archimedean collar (Gamma) enters `h⁰`. A proof that no lattice-count `h⁰`
  exists even there would retire the geometric producer over ℤ.

**Q2. How do the primes enter the Euler characteristic of a test cycle without breaking the Riemann
inequality?** On the scaling surface `f·g` contains the prime comb. Over `𝔽_q` the corresponding
term is the fixed-point count of the Frobenius graph, and RR keeps it in `χ` through the Lefschetz
formula.

What is in hand [L/M]:
- subtracting `ψ` from the polar box breaks the Riemann inequality;
- linear theta RR does not give the quadratic inequality;
- positive counts, determinant data, Boolean sections, majorants and finite readings cannot supply
  Bézout;
- exact source effectivity needs infinitely many degrees;
- the counterterm is self-similar exactly for `Λ` (`Λ ∗ 1 = log`).

Why: every naive construction has failed at this point. Any `h⁰` that passes must make the explicit
formula appear as the duality of the graph class, which is also where selection (Γ) and precision
(Π) would be paid. The question has a decisive negative form: classify the lattice-count `h⁰` whose
`χ` contains `Σ Λ(n)…` and test whether any of them satisfies RI.

**Q3. Can the Hodge defect be read as an integer uniformly in height?**

What is in hand [L]:
- integer-theta Fredholm indices equal the collision charge;
- the source-only stopping rule is sound and eventually complete;
- `κ ≤ sup O`; `O ∈ 2ℕ`; RH ⇔ every window index `< 2`.

The obstruction is the scale of the certificate: window-boundary moduli of finite theta amplitudes
and divisor separation. The first stabilized prefix is unbounded in height.

Why: quantization is the only mechanism that converts an `O(1)` bound into RH. A height-uniform
reading (prefix polynomial in height, explicit boundary placement) would turn RH into the vanishing
of an explicit integer-valued function of finitely many theta values. A source bound of precision
`O(1)` would then suffice. The input it needs (separation or boundary-modulus lower bounds) is
logically independent of RH. Answering the question decides whether an `O(1)`-precision producer
can exist at all.

## 2.4 A wildly different route

**I see none that avoids the three walls.** A route outside the corpus's families would need an
exact positivity source. The exact sources available over ℤ are:
- Poisson summation / theta modularity;
- the divisor identity `Λ ∗ 1 = log`;
- the CRT incidence squares;
- positivity of the Gamma factor;
- the Euler product;
- self-adjointness of the Laplacian on `SL₂(ℤ)\ℍ`.

Every route and candidate in the corpus already draws on these. Candidates examined:
- **Total positivity by planar networks.** The Taylor data of `Ξ(√−z)` is a positive mixture of
  PF∞ sequences, and total positivity is preserved by products and compositions, not by sums.
- **Interlacing families / finite free probability on Jensen sections.** We have
  `J^d_Ξ(X) = E_U[p_d(U²X)]`, and real-rootedness for all `d` is Pólya–Schur's multiplier-sequence
  form of RH. Representation by expected characteristic polynomials is tautological for real-rooted
  polynomials. No source structure.
- **Ergodic rigidity of `(×p, ×q)`.** A positive realization of the coupling is the sign itself.
- **Lee–Yang, prolate operators, Bost–Connes KMS states.** Already present as W1C, the retired
  label B, and APD.
- **Indefinite theta series (Zwegers–Vignéras completions).** They would supply a Poisson summation
  for a Lorentzian lattice, the form a surface Serre duality must take. That is a tool for Q1–Q2
  and the RR branch, not a separate route.

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — effectivity on prime-free cycles
**Question.** Construct an arithmetic effectivity on the prime-free cycles of the scaling surface
(B39, Q1), and derive prime-free Weil positivity from Riemann–Roch.
- **Below RH.** The target positivity is already known; nothing about zeros is asserted.
- **Advance.** It would be the first Hodge index over ℤ obtained from sections rather than signs.
  It would test whether Weil's architecture exists over ℤ at all, and it is the base case of
  2.6.1.
  - Its natural extension adds the prime `2` (radius `181/500`, where Weil floors are proved) and
    then `3` (A12), one prime at a time.
  - Each step is a finite-aperture statement that is true if RH is, yet its proof by RR is
    uniform in a way estimates cannot be (Picture 3).

### 2.5.2 Route PM — a Hermitian structure on the regularized Mayer operator at the Maass line
**Question.** Construct a sesquilinear (Lewis–Zagier type) structure on eigenfunctions of the
regularized Gauss–Mayer operator `R(w)` near `Re w = 1` (`w = 2s`; the Maass line `Re s = ½`) that
makes the eigenvalue-±1 problem self-adjoint there, including the Eisenstein (scattering) sector.
Derive `ζ(1 + it) ≠ 0` and a zero-free region near `Re s = 1` from it.
- **Below RH.** It gives a classical-type zero-free region.
- **Advance.** PM's operator side has no positivity structure yet.
  - Contraction or cone methods cannot separate eigenvalue ±1 on the Maass line, where it occurs
    densely, from just left of it; a Hermitian structure can.
  - It would be the first unconditional statement about zeros from PM's own operator, and the
    template for 2.6.2.
  - It needs A23 (Mayer–Selberg and scattering identities) as input.

### 2.5.3 Route WD — critical-scale clustering
**Question.** Prove `o(log U)` for the dyadic mean of the unit-window Hecke defect at one
`c < 22/51`. Equivalently, for every `κ > 0`, all but `o(V log V)` zeros up to `V` lie within
`κ/log V` of the line [L].
- **Below RH.** It implies neither Lindelöf nor a zero-free region. Every pointwise step on WD's
  ladder is at least qRH (Picture 12), so this mean statement is the route's only sub-qRH step.
- **Advance.** It closes the `loglog` factor between the proved almost-all corridor
  `(6/5)loglog T/log T` and the critical scale [L]. Classical near-line density bounds give a
  proportion decaying in `κ`, not `o(1)`.
  - The input must be a mollifier gain that tends to zero on the near-line shells (scales I and II
    of the three-scale mollification), i.e. arithmetic acting on the conjugate diagonal's mean.

### 2.5.4 Route HF — an exact certificate at the first two-prime window
**Question.** Prove Weil positivity on the first window where two primes interact (radius just above
`½ log 3`: primes `2`, `3`, prime power `4`) by an exact identity assembled from HF's exact pieces,
not by numerics. The pieces are:
- jump squares (`Λ ∗ 1 = log`);
- CRT affine incidence squares;
- the Gamma form and the pole hyperbolic pair;
- coupling differences `(T_{2^a} − 1)(T_{3^b} − 1)f`.
- **Below RH.** It is a finite-aperture statement with an `O(1)` margin. The doubly exponential
  ceiling bites only from `A ≈ 3`.
- **Advance.** It would be the first exact payment of a cross-prime coupling. The coupling on one
  two-prime lattice decides RH [L], and over a curve the same statement is Castelnuovo–Severi on
  the Frobenius span [L].
  - Whether the certificate's pattern persists as the window grows inside `⟨2, 3⟩` is B7, i.e.
    RH.
  - It tells HF whether its exact identities can carry primes jointly, which the packet identity
    does only up to the shell degree.

## 2.6 Breakthrough questions that open the path to RH

### 2.6.1 Whole programme — the effective cone of the scaling surface
**Question.** Construct an effectivity on all cycles `aH + bV + f` of the scaling surface with the
Riemann–Roch and ample axioms: an arithmetic `h⁰` with Serre duality, the quadratic RR lower bound
along rays and subquadratic growth in degree zero.
- **Why it opens the path.** RH ⇔ such an effectivity exists [L] ⇔ quadratic RR [L]. Over `𝔽_q`
  this one object resolves all three walls:
  - Hodge index gives the sign;
  - Castelnuovo–Severi gives the precision `|N − q − 1| ≤ 2g√q`;
  - the Frobenius graph is the canonical selector.
- Over ℤ the base and pole-plane cases exist [L], and the failure modes are catalogued (Q2). The
  remaining step is a definition with identities (Poisson-type Serre duality whose dual side is the
  explicit formula), not an estimate.

### 2.6.2 Route PM — the Hermitian structure at the resonance line
**Question.** Extend the structure of 2.5.2 to the resonance line `Re w = ½` (`Re s = ¼`). The
regularized operator `R(w)` should be self-adjoint, or J-self-adjoint with J definite on the
resonant sector, so that eigenvalue ±1 in `½ < Re w < 1` occurs only on the line.
- **Why it opens the path.** With A23, ζ zeros in the strip are the eigenvalue-±1 events of `R(w)`.
  Partner saturation is RH [L], and definiteness would force it.
- The structure must come from the operator: no algebraic map takes the critical parabola to a real
  spectrum [L].
- The corpus also records that positive resonant norms and the partner-saturation receiver do not
  select zeros by themselves [M]. The question is the missing structure, nothing less.

### 2.6.3 Route WD — quantized reading with an `O(1)` source bound
**Question.** Find a height-uniform integer reading of the window collision charge (B40). Then bound
that integer by a source quantity that is `< 2` with `O(1)` precision.
- **Why it opens the path.** RH ⇔ every window index `< 2` [L]. Quantization removes the
  doubly-exponential precision requirement that blocks estimates. The two remaining inputs are
  precise:
  - a separation or boundary-modulus bound, independent of RH;
  - an `O(1)` bound for an explicit integer built from theta values.
- No other route has a reduction of RH to an `O(1)`-precision statement about computable integers.

### 2.6.4 Route HF — an exact SOS identity on one two-prime lattice
**Question.** On `⟨p⟩ × ⟨q⟩`, is Weil's dilation form on boost-mass-zero vectors a sum of squares
of coupling differences `(T_{p^a} − 1)(T_{q^b} − 1)f` plus the Gamma form, at every window size
(B7)?
- **Why it opens the path.** Bounded coupling on one two-prime lattice is RH [L]. The polarization
  `C_K(u, v) = B(T_{u⁻¹}f − f, T_v f − f)` supplies the natural squares [M], and
  `κ(L_pL_qK_ζ) = κ` [M].
- Over a curve the bounded coupling is Castelnuovo–Severi on the Frobenius span [L]. That is the
  effectivity of 2.6.1 restricted to the span of two Hecke correspondences. 2.6.4 is the
  identity-level form of 2.6.1 on the smallest carrier of the full index, and 2.5.4 is its first
  window.

## 2.7 Does closing RH need a new field?

**Assessment: yes — an effectivity theory for the scaling surface of ℤ, with quantization as its
index-theoretic companion.**

*Why this field and not another.* Three facts decide it:
- The doubly exponential aperture ceiling [L] rules out every estimate-based producer.
- The scaling surface reduces RH exactly to the existence of an effectivity with RR and ample
  axioms [L], and refutes positivity-defined cones [L]. Effectivity must come from sections, not
  from signs.
- Over `𝔽_q` the same structure (RR on `C × C`, Frobenius graph) resolves sign, precision and
  selection at once.

The corpus has the base of this theory: the theta `h⁰`, RR on `Spec ℤ` and on the pole plane, the
polar-surface axioms. It lacks the test classes.

*What it is about.* Divisors on the scaling surface:
- the pole plane `aH + bV`;
- test classes `f`, standing for correspondences: graphs of scaling and of Hecke dilations;
- their sections `h⁰`, defined arithmetically as logarithms of weighted counts of lattice points,
  so that `h⁰ ≥ 0` and monotonicity are free;
- the Euler characteristic `χ`, which must contain the explicit formula as a Lefschetz term;
- Serre duality, a Poisson summation on a two-dimensional object.

The intersection form is Weil's: `f·g = B(f)A(g) + A(f)B(g) − Re W(f,g)`. The primitive part is
`v₁^⊥`.

*What it would be like.* Weil's proof transplanted:
- RR (identity) + ample class ⇒ Hodge index ⇒ Castelnuovo–Severi ⇒ bounded coupling ⇒ RH.
- Quantization is the integer side: the Hodge defect is the even integer that RR must show is
  zero, and its readings (collision charge, heat collisions) give the field `O(1)`-precision
  checks.
- Over a curve the theory is classical. Over ℤ the genus is infinite, so RR must be an identity
  valid at every degree; no truncation decides.

*Criteria it must meet.*
1. `h⁰` defined from arithmetic (counts or volumes), not from the sign of `W`, with
   `h⁰ ≥ 0`.
2. Serre duality by an identity (Poisson-type).
3. The Riemann–Roch and ample axioms of the polar surface, with the quadratic lower bound along rays
   and subquadratic growth in degree zero.
4. The prime comb appears in `χ` exactly as in the explicit formula.
5. It avoids the proved no-gos:
   - functions of finite readings and mass;
   - positive counts, determinant data, Boolean sections, majorants;
   - polar box minus `ψ`;
   - finitely many degrees;
   - positivity-defined cones.
6. Selection: it fails for prime-flip twins, for functional-equation twins without Euler product and
   for the golden curve datum. Over `𝔽_q` it reproduces Weil.
7. Consistency with quantization: the defect it forces to zero is the even integer read by
   collision charges.

*Questions it must answer.*
- What is the section space of a test class: which lattice (`ℤ²`, adelic, split or definite form)
  and which metric? The Gamma factor should appear as the Gaussian weight.
- Is surface Serre duality a two-dimensional Poisson summation for an indefinite (Lorentzian)
  lattice? Lorentzian theta series need Zwegers–Vignéras completions, which can be negative. Is
  the explicit formula the dual side?
- Why ζ and not an Epstein zeta? Positive-definite binary thetas give Epstein zetas with off-line
  zeros, so the surface must be the split one.
- What is the effectivity of a Hecke correspondence `T_p` (a boost on the pole plane [M])?
- What replaces finite genus over ℤ?

*Tools it aims to develop.*
- Two-dimensional arithmetic Poisson summation and indefinite theta series.
- Arakelov-type `h⁰` beyond the base (van der Geer–Schoof, Groenewegen) on products.
- The polar-surface axiom calculus already in ACS.
- Index readings (Fredholm collision index, heat collisions) as consistency checks.
- Function-field calibration through RR on `C × C` and Stepanov counts.

*Objects, language, mechanisms.*
- Objects: scaling surface, pole classes `H, V`, test and graph classes, canonical class `K`, theta
  `h⁰`, Euler characteristic with Lefschetz term, effective cone, ample class, primitive part, Hodge
  defect.
- Mechanisms: Poisson duality ⇒ RR; RR + ampleness ⇒ Hodge index; Hodge index on the span of two
  Hecke correspondences ⇒ bounded coupling ⇒ RH.

No corpus result shows that such an effectivity exists for ζ. Its first test is Q1 / 2.5.1 on
prime-free cycles, where existence is not obstructed by zeros.
