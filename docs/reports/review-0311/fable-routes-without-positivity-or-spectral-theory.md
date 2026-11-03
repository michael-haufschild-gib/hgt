# Proof routes that survive without positivity and without spectral theory

Companion to `fable-routes-without-weil-positivity.md` (the weaker assumption) and `fable.md`.
Evidence tags as there: `[L]` Lean, `[D]` derived, `[C]` proposal, `[N]` numerical.

---

## 0. The assumption and its reading

**Assumption.** (i) No argument whose core is the nonnegativity of an RH-equivalent object closes:
Hermitian forms (Weil, Li, Herglotz, Krein, Hankel), determinantal and total positivity
(Laguerre–Pólya, Pólya frequency, Lee–Yang, real-rootedness), cones (Weil cone, blind cone).
(ii) No argument whose core is the spectrum of an operator closes: Hilbert–Pólya realizations,
Mayer/Lewis transfer operators, Selberg trace formulas, Maass and Eisenstein spectral expansions,
Krein–Langer index theory, Pontryagin extensions, canonical systems.

**Reading.** The exclusion is of *mechanisms*, not of tools. Jensen's formula, the subharmonicity
of `log|ζ|`, Fejér kernels and the Cauchy–Schwarz inequality remain usable as steps; what cannot be
the engine is a statement "an RH-equivalent form is nonnegative" or "an operator attached to `ζ`
is self-adjoint".

**What the corpus says about the remaining space.** The walls Σ, Π, Γ are one obstruction `[L]`;
removing the positivity and spectral shapes leaves the estimate shape (Π), the rigidity shape (Γ),
zero-location statements, geometric function theory, recurrence, and combinatorial or
additive-combinatorial reformulations. Everything below meets the same wall; the point of this
document is to say in which coordinates.

Removed beyond the previous document: §3 of that document (real-rootedness and Lee–Yang), §2.5
(Krein–Langer zero–one law, which is index theory), PM/RN/W1C/PTR (spectral realization), the
horocycle and crystalline-measure proposals in their spectral/positivity forms, and the Newton-disc
and Nevanlinna routes insofar as their engine is a Laplacian sign (kept below with that caveat).

---

## 1. Estimate routes (Π)

Unchanged in substance from the previous document §1; listed with what is non-spectral and
non-positive in each.

| Route | RH-equivalent statement `[L]` | Engine | Open estimate |
|---|---|---|---|
| MC | `M(x) = O(x^{1/2+ε})`; `det R_N = M(N)` | cancellation of a signed sum | the trivial gauge point (Γ1) |
| WL/CAF | first cyclotomic band energy `O(N^{1+ε})` | `L²` energy of one packet; Mellin ODE | signed square-root precision |
| Two-site band / ACoT | `|c_ψ(t)| < Q(ψ)` read as `|smoothed count − AB e^{t/2}| < Q(ψ)`; bounded two-prime coupling ⇒ RH or no deepest zero | exact identity of the entry; boundedness along two primes | the sharp constant |
| PBM | regularized prime/log-ζ series converges for `σ > ½` | Dirichlet convergence | coefficient cancellation |
| RB | Robin / Nicolas / Lagarias inequalities | elementary inequality at extremal integers | square-root remainder of the Mertens product |
| FU/CFC/RP/LI/SZ | explicit-formula functionals bounded below | one joint bound | seed, drift, covariance, endpoints |
| CHMD | causal prime wave bound | operator-norm estimate `O(e^{−√log Y/C})` `[L]` | unnormalized error |
| WD caps | right-port flux through `[½, σ_m]` cancels at every polynomial stage | contour flux of `ζ'/ζ` | zero-rate port bound |
| Hardy–Littlewood | `H(x) = O(x^{−1/4+ε})` | entire series of `1/ζ(2k+1)` | MC in disguise |
| Nyman–Beurling | approximation error `→ 0` | Hilbert-space approximation | MC with natural coefficients |
| Franel–Landau | `Σ δ_ν² = O(n^{−1+δ})` | Farey discrepancy | MC on `SL₂(ℤ)` |

Walls, all `[L]`: the parity barrier at damping `½`; the precision class (parity-breaking,
twist-stability-breaking input required); every cyclotomic band has abscissa `2Θ`; Haar-a.e. and
Baire-generic gauge behaviour do not control the trivial point; Vaughan endpoints, gauge averages,
single-height savings and stronger-than-half-power targets are killed.

What a Π proof must do: produce square-root cancellation at every scale with the sharp constant,
by an identity that breaks parity at first order. No such identity is known in any field.

---

## 2. Rigidity routes (Γ), non-spectral

| Route | What is proved `[L]` | What a proof must do |
|---|---|---|
| SEL Selberg-class rigidity | degree gap; degree `< 1` is the unit; strong multiplicity one at the critical Euler abscissa for arbitrary Gamma data; finite-prime rigidity; degree-one conductor/pole dichotomy; positive multiplicative twins with zeros at any `Re s ∈ (½,1)` violate only `θ < ½` | an identity for degree-one full Selberg functions that an off-line quartet contradicts, using the strict Euler bound essentially |
| APD/Beurling | FE + positive measure ⇒ counting measure of `ℕ`; discrete Beurling + FE ⇒ rational primes; continuous Beurling systems admit zeros in `(½, 2/3)` | nothing: these fix the minimal input |
| Pre-divisor forcing (C10) | exact receivers for APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF; each lacks zero-independent forcing | a section defined before the divisor that forces the zeros |
| Band holomorphy `Λ(s)/Λ(s+1)` (B31) | RH-equivalent | holomorphy of a quotient from the Euler product |
| ART | no realization of `ζ` by dynamics except commutative | closed as an input |
| Hypertranscendence | `ξ` hypertranscendental unconditionally; not an independent RH input | closed as an input |

What a Γ proof must do: use the functional equation and the Euler product with the strict Euler
bound together, and fail on the twins, flips, shifted products and Epstein data `[L]`.

---

## 3. Zero-location routes

- Density: Guth–Maynard Theorem 1.1 and its corollaries; Vinogradov–Korobov; Backlund converses
  (off-line sparse ⇔ Lindelöf); WD's eight-way equivalence and double-log certificates `[L]`.
  Reach: `100%` clustering, Lindelöf-depth statements; never absence.
- Speiser: RH ⇔ `ζ' ≠ 0` on `0 < Re s < ½`; exact counts between unshadowed heights; deficit
  `≤ ((1 − HD1)/2 + ε)N(T)` `[L]`. Engine: the argument principle on rectangles with the sign law
  `Re ζ'/ζ < 0` on the boundary `[L]` (a sign of a logarithmic derivative on a contour, not of a
  form).
- What a location proof must do: a zero–one law without index theory. The analytic form is
  Backlund's: a single off-line zero at height `T` with the known count `N(T)` and the Vinogradov–Korobov
  growth bound `‖ζ‖ ≤ C log τ` near `σ = 1` `[L]`; what is missing is a growth bound near `σ = ½`
  that one off-line zero violates. That is Lindelöf-type input (Π).

---

## 4. Geometric function theory

- Speiser (above).
- Balazard–Saias–Yor / Volchkov: RH ⇔ `∫ log|ζ(½+it)| dt/(¼+t²) = 0`; the integral is the right-zero
  sum `2π Σ log|ρ/(1−ρ)|` `[L]`. Engine: Jensen's formula (an identity). What a proof must do:
  evaluate the critical-line log-integral exactly; its dyadic pieces are the Littlewood edge
  budgets `[L]`, and one dyadic constant is RH (Π5).
- Nevanlinna/Tsuji theory in the half-plane: second-main-theorem chain and Poisson–Jensen bounds
  exist `[L]`; a criterion would say the value `0` is totally deficient for `ζ` on `Re s > ½`.
  Caveat: the engine is the subharmonicity of `log|ζ|`, a positivity of the zero measure, not of an
  RH-equivalent form.
- XN Newton discs: kept with the same caveat (nonnegative Laplacian of the interior margin).

---

## 5. Recurrence

- BAG: RH ⇔ strong recurrence of `ζ` on every closed disc of the strip `[L]`. Engine: Bohr
  almost-periodicity and Kronecker; what is missing is recurrence to targets that are themselves
  zeros `[L]`. Non-spectral, non-positive; Π in content (approximation of `ζ` by its shifts).

---

## 6. Alternatives not yet explored (non-positive, non-spectral)

All `[C]`; corpus search results as in the previous document.

### 6.1 Discrete Morse theory on the divisibility nerve
- Target: `|M(N)| = |χ(nerve)| ≤ #critical cells` of a Morse matching `[L: HWV for χ = M(N)]`.
- First theorem: a matching on the divisibility–successor complex of `[1,N]` whose critical cells
  lie on the gcd strata, with a count `N^{1/2+ε}`.
- Why it is neither positivity nor spectral: it is a cancellation count by an explicit involution.
- Risk: the count of critical cells on the top coprime stratum is the open core B9 in a different
  coordinate; a power saving is plausible, square-root precision is Π.

### 6.2 Sign-reversing involutions for the Redheffer determinant
- Target: `det R_N = M(N)` `[L: ADT]` as a signed count of nonintersecting path systems
  (Lindström–Gessel–Viennot) on the divisibility digraph; an involution cancelling all but
  `N^{1/2+ε}` systems.
- Why new: no corpus module; the determinant is used only as an identity.
- Risk: the surviving systems are indexed by squarefree supports, so the fixed-point count is
  `Σ μ` over a structured subset; the involution must act across dyadic scales to beat the trivial
  bound.

### 6.3 Self-repulsion of an off-line quartet
- Target: an exceptional-zero repulsion law for `ζ` alone: an off-line zero of depth `δ = β − ½ > 0`
  at height `γ` forces a zero-free region of width `≫ δ` (in mean-spacing units `δ log γ`) around
  height `γ` on the line, contradicting the local count `N(γ + h) − N(γ) ≈ (h/2π) log γ`.
- Tools in Lean: Turán power sums `[L]`, Speiser disks and sign laws `[L]`, the Vinogradov–Korobov
  growth bound `[L]`, Montgomery–Taylor proportion `[L]`.
- Why new: the corpus has Diophantine prime repulsion and the ACoT boundary repulsion, no
  zero–zero repulsion.
- Risk: every known repulsion is pole-driven (`c/log t`) or cross-L-function (Deuring–Heilbronn);
  a quartet is consistent with all proved statistics. The first test is numerical `[N]`: measure the
  local gap statistics the explicit formula would force near a hypothetical quartet.

### 6.4 Fourier interpolation and strip uniqueness
- Target: an interpolation basis for functions analytic in a strip with nodes at the zero
  ordinates and at `±log n`, in which the explicit formula is one relation; a uniqueness theorem for
  the Dirichlet-series kernel that forces the nodes real.
- Why new: no interpolation-basis or Beurling–Malliavin module.
- Risk: without positivity the uniqueness question is the zero-free property of the kernel on the
  strip, which is Γ; with positivity it is P2. The first theorem is the duality statement itself
  (nodes of one basis are zeros of the other's kernel) for the Weil kernel of the corpus.

### 6.5 Sum–product estimates on the top coprime stratum
- Target: estimate the coupling of coprime atoms at ratio `|log(m/n)| ≲ 1/c` by multiplicative-energy
  inequalities for `ab − cd = 1`; Kloosterman and Estermann modules exist `[L]`.
- Why new: no sum–product module; `additiveEnergy` appears only inside Guth–Maynard.
- Risk: power savings only; the critical curve needs the constant `κ₀` `[L: HWV]`.

### 6.6 Statistics of `log|ζ|` on the line
- Target: prove the critical-line log-mean `(L)` from a central limit theorem with a rate, closing
  the density branch (`100%` clustering) `[L: CDG equivalences]`; then the BSY equality from the
  exact mean.
- Why new: no central-limit-theorem module; Jensen and second-moment bounds exist `[L]`.
- Risk: the CLT controls the distribution, not the mean to `o(1)`; the mean is `Σ(β − ½)` by
  Littlewood's lemma, so the exact mean is the statement itself.

### 6.7 Symmetric Riemann–Siegel approximants
- Target: zeros of `A(s) + χ(s)A(1−s)` lie on the line by modulus domination; RH from a floor
  `||A(s)| − |χ(s)A(1−s)|| > |R(s)|` off the line.
- Why new: `RiemannSiegelLeeYangChain`, `RiemannSiegelThresholdLaw`, `ZetaNotchCriticalAFE` exist;
  no approximant-zero module.
- Risk: the floor vanishes at the approximant's own zeros; the structure of zeros of symmetric
  Dirichlet polynomials is a Lee–Yang phenomenon (excluded as engine, usable as a fact).

### 6.8 Dynamical reformulations without spectral proofs
- Zagier–Sarnak horocycle rate `O(y^{3/4−ε})` ⇔ RH; Möbius disjointness and Chowla-type statements
  (`ae_moebius_chowla` on the gauge torus `[L]`).
- Why kept: the statements are dynamical; the engine would have to be an effective equidistribution
  argument without the spectral expansion. None exists with an error term.

### 6.9 Combinatorial explicit formula on the window algebra
- Fact: Weil's window form is an explicit signed combination of projective point counts
  `φ(m)#ℙ^{j−1}(ℤ/m)` with the Lagrange coefficients of `log` as signs `[L: WTZ]`; `ζ` on a window is
  the plethystic exponential of the primes; `Λ` is a sum of Adams operations `[L]`.
- Target: a bijective or involutive proof of a cancellation identity among these counts that does
  not pass through positivity, e.g. an exact evaluation of the signed count on the rational lattice
  (where folds count multiplicative pairs `[L]`).
- Risk: the signed count's sign is RH; an exact evaluation is an identity whose nonnegativity is
  the Σ wall. Only a count identity with a visibly nonnegative right-hand side would help, and
  finite count identities are excluded at the first prime `[L]`.

---

## 7. Assessment

1. Under the stronger assumption the surviving routes are the estimate routes (§1), the
   non-spectral rigidity routes (§2), the zero-location ladder with an analytic zero–one law (§3),
   the log-integral identities of §4, Bagchi recurrence (§5), and the combinatorial,
   additive-combinatorial and interpolation alternatives of §6.
2. Every one of them is Π or Γ in content. The corpus has proved the exact forms of both walls on
   the estimate side (parity at damping `½`, precision class, band abscissa `2Θ`, gauge trivial point)
   and on the rigidity side (positive twins at `3/4`; FE + Euler product minimal). The assumption
   removes the shapes in which the function-field proofs were written; it does not remove the wall.
3. The three alternatives with a definable first theorem are §6.1 (a Morse matching critical
   exactly on the gcd strata), §6.3 (an exceptional-zero repulsion law for `ζ`), and §6.4 (the
   duality theorem for the explicit-formula kernel). Each would be new mathematics even if it stops
   short of RH; none has a known mechanism for square-root precision.
