# The parity vortex of the squarefree Gibbs gas

- **ID:** `squarefree-gibbs-parity-vortex`
- **Stage:** 1-in-progress
- **Type:** THEOREM (new structural law) + OPEN CORE (infinite-volume seam-flux)
- **Parent:** `route-e-squarefree-exponential-gibbs-parity.md` (the (G2) card) — this card
  turns its asserted mechanism ("three primes destroy real stability; the attack must use
  the multiplicative cutoff boundary") into exact theorems and locates the seam-flux
  observable geometrically.
- **RH used:** no.  All theorems below are unconditional and finite.

## The object

For a finite set `S` of distinct primes (any pairwise-coprime integers ≥ 2 work), `x > 0`:

```text
P_S(z, x) := Σ_{T ⊆ S} z^{|T|} · exp(−x·Π_{p∈T} p),     k := |S|,  m := Π S.
```

This is the diagonal of the partition polynomial of the *multiplicative-energy* lattice
gas (energy of a configuration = product, not sum, of occupied primes — the Laplace/Gibbs
cutoff `e^{−nx}` of Route E).  Its parity point is `z = −1`:

```text
P_S(−1, x) = Σ_{n | m} μ(n) e^{−nx}   — the finite Möbius–Laplace current.
```

The (G2)/RH frontier is the `S → all primes` current at scale `x^{1/2}`.

## Theorems (paper proofs complete; dependency-closed)

**T0 (cutoff recursion).**  `P_{S∪{p}}(z, x) = P_S(z, x) + z·P_S(z, p·x)` for `p ∉ S`.
*Proof.* Split `T` by `p ∈ T`; `e^{−x·p·ΠT'} = e^{−(px)·ΠT'}`.  ∎
This is the "multiplicative cutoff boundary" of the parent card as an exact two-scale map:
adjoining a prime couples the ensemble to itself at the dilated scale `px`.

**T1 (two-prime Lee–Yang, all x).**  For distinct `p, q ≥ 2` the quadratic
`P_{p,q}(·,x)` has two distinct real negative roots for every `x > 0`:

```text
Δ₂ = (e^{−px} + e^{−qx})² − 4e^{−pqx} ≥ 4e^{−(p+q)x} − 4e^{−pqx} > 0
```

by AM–GM and `p + q < pq` (i.e. `(p−1)(q−1) > 1`).  ∎

**T2 (parity-jet law).**  Substituting `z = −1 + w`:

```text
P_S(−1+w, x) = Σ_T (w−1)^{|T|} e^{−x·ΠT};      at x = 0 this is  w^k;
∂_x|_{x=0} P_S(−1+w, x) = −Σ_T (w−1)^{|T|} ΠT = −Π_{p∈S} (p·w − (p−1)).
```

(The product identity is `Σ_T Π_{p∈T} a_p = Π_p (1+a_p)` at `a_p = p(w−1)`.)  Hence the
exact first-order law at the parity point:

```text
P_S(−1+w, x) = w^k − x·Π_{p∈S}(p·w − (p−1)) + R,   |R| ≤ (x²/2)·Π_p(1 + p²|w−1|),
```

using `0 ≤ e^{−u} − 1 + u ≤ u²/2`.  Consequences: the resolvent polynomial
`R_S(w) = Π(pw − (p−1))` has all roots real in `(1/2, 1)` at `w_p = 1 − 1/p`; its value at
the parity point is `R_S(0) = (−1)^k φ(m)` — **Euler's totient is the vortex intensity**:

```text
P_S(−1, x) = (−1)^{k+1} φ(m)·x + O(x²).
```

**T3 (parity-vortex theorem, k = 3).**  For any distinct primes `p, q, r` and all
sufficiently small `x > 0`, `P_S(·,x)` has exactly one real and two strictly complex
roots: writing `P_S(−1+w,x) = e₃w³ + e₂w² + e₁w + e₀`, the cubic discriminant obeys

```text
Δ(x) = −27·φ(pqr)²·x² + O(x³) < 0,
```

because `e₀ = φ(m)x + O(x²)`, `e₁ = −(3σ₃−2σ₂+σ₁)x + O(x²)`, `e₂ = (3σ₃−σ₂)x + O(x²)`,
`e₃ = 1 + O(x)`, so every discriminant monomial except `−27e₃²e₀²` is `O(x³)`.  A real
cubic with three real roots has `Δ = e₃⁴·Π_{i<j}(r_i−r_j)² ≥ 0` (Vieta ring identity), so
`Δ < 0` excludes any real factorization.  ∎

**T3′ (current–discriminant identity, exact).**  For the monic-normalized cubic jet,

```text
27·e₃²·e₀² = −Δ + 18·e₃e₂e₁e₀ − 4e₂³e₀ + e₂²e₁² − 4e₃e₁³ .
```

The squared parity current is an explicit polynomial in the higher jet and the
discriminant.  Real-rootedness (`Δ ≥ 0`) FORCES the current bound
`27e₃²e₀² ≤ 18e₃e₂e₁e₀ − 4e₂³e₀ + e₂²e₁² − 4e₃e₁³`; conversely a large current forces
`Δ < 0` — the vortex.  **Any lower bound on the cluster discriminant is an upper bound on
the parity current.**  This is the seam-flux observable in exact algebraic form: a
sign-definite functional (a discriminant — a squared zero-repulsion) that reads the
coherent current, structurally outside the mean-square σ-algebra.

**T4 (general k ≥ 3 vortex; Hurwitz form).**  Rescaling `w = x^{1/k}·ω`, the parity
cluster converges to the regular star `ω^k = (−1)^k φ(m)`: a `k`-gon of radius
`(φ(m)·x)^{1/k}` centered at the parity point, of which at most two vertices are real.
So for every `k ≥ 3` at least `k − 2` roots are strictly complex for small `x`: Lee–Yang
reality fails maximally — the parity point is a **vortex center of charge k**, not a
Lee–Yang point.

## What is new (relative to literature and corpus, July 2026)

- The Lee–Yang/primon-gas literature (Julia, Spector; Yang–Lee theory surveys) treats
  Dirichlet-weighted arithmetic gases `n^{−s}`, whose partition polynomials factor over
  primes and have trivially real zeros.  The Laplace-weighted (multiplicative-energy)
  gas does not factor; its parity-point zero geometry — the vortex law, the totient
  intensity, the current–discriminant identity — appears in no literature found.
- The corpus's (G2) card asserted "two-prime tables strictly Rayleigh, three primes
  destroy real stability" without proof.  T1/T3 prove the diagonal form exactly and
  identify the *mechanism*: the parity current itself is the obstruction
  (`Δ ≈ −27·current²`), and the failure is maximal (equiangular star), not marginal.
- Consequence for Route E: every real-stability / strong-Rayleigh / negative-dependence
  route to (G2) is dead structurally (not merely unverified): the parity evaluation
  point is a vortex center for `k ≥ 3`.  The surviving mechanism is exactly the T0
  two-scale recursion (the cutoff boundary) and the T3′ geometry: parity cancellation
  ⟺ zero-repulsion lower bounds at the parity cluster.

## [OPEN CORE]

The infinite-volume seam-flux law: a lower bound on the parity-cluster discriminant
(zero-repulsion) of the full ensemble `Σ_{n squarefree} z^{ω(n)}e^{−nx}` at scale `x`,
strong enough that T3′-type identities bound the current by `x^{1/2−ε}·Z(x)`.  At full
strength this is (G2) = RH; partial repulsion bounds give partial current bounds — a new
graded route whose rungs are geometric (cluster separations), not zero-free regions.

## Falsifiers / hostile tests

- T1–T3′ are finite and exact; any arithmetic error falsifies on a 3-prime instance.
- The vortex must NOT be an artifact of the diagonal: the multivariate polynomial already
  fails real stability at 3 primes (Rayleigh violation exists), consistent.
- If some literature source is found with the multiplicative-energy gas zero geometry,
  the novelty claim retracts to the current–discriminant identity and the Route E link.

## Log

- 2026-08-05 — card created; T0–T4 paper-proved (this card, self-contained); SOTA search
  (Lee–Yang × Möbius/squarefree; ω-generating polynomials): no overlap found.  Next:
  Lean formalization of T0, T1, T2 (eval-level), T3, T3′ (ring identities + limit-form
  discriminant negativity), unconditional.

## 2026-08-05 FORMALIZED: `RHTower/GibbsParityVortex.lean`

Wired into `RHTower.lean`; targeted build 8655 jobs; axioms only
`propext, Classical.choice, Quot.sound`; zero warnings.  Namespace `RHTower.GibbsGas`:

- `gibbsDiag` (the gas), `gibbsDiag_insert` (**T0**, the cutoff recursion),
  `gibbsDiag_zero` (free limit `(1+z)^k`), `gibbsDiag_singleton`;
- `hasDerivAt_gibbsDiag_parity` (**T2**, the parity-jet law: coupling-derivative
  `−∏(pw−(p−1))` at the shifted parity point) and `hasDerivAt_gibbs_current`
  (`(−1)^{k+1}∏(p−1)`: the totient intensity);
- `two_prime_real_rooted` (**T1**: explicit distinct real roots, AM–GM discriminant);
- `cubic_vieta` (Vieta from a pointwise factorization, by `linear_combination` at
  `w = 0, ±1`), `cubic_discrim_nonneg_of_real_rooted` (`Δ = a₃⁴·∏(rᵢ−rⱼ)²`),
  `current_sq_le_of_real_rooted` (**T3′**, the current–discriminant inequality);
- `parity_vortex_three` (**T3**: `∀ᶠ x in 𝓝[>]0`, no real factorization of the parity
  cubic — via `Δ(x) = x²·G(x)`, `G → −27φ² < 0` by slope limits, and the Vieta
  discriminant identity).

Lean traps: `set`-bound reals are opaque to `ring` (unfold with the defining equation
before `convert`-free value rewrites); a `HasDerivAt` chain's function/value trees must be
mirrored exactly (build the value by a `show ... from by ring` rewrite, not `convert`);
`Finset.sum` of function-valued summands needs `congr_of_eventuallyEq` + `Finset.sum_apply`
to become a `HasDerivAt` of the pointwise sum; `simp` leaves numerals like `−1−1+3−1`
unevaluated (finish with `norm_num`); `{q} ≠ insert q ∅` syntactically.

- 2026-08-05 — T0–T3′ formalized unconditionally; T4 (general k, Hurwitz form) remains
  paper-level on this card.

## 2026-08-05 THE TWO-SCALE REPULSION PROBLEM: SOLVED (locking law)

**Question.**  What does T0 force about the separation of the parity cluster — can
cluster discriminants be lower-bounded inductively across the prime ladder?

**Answer (three theorems).**

**R1 (current two-scale law).**  Evaluating T0 at the parity point:
`J_{S∪p}(x) = J_S(x) − J_S(px)` — the Möbius–Laplace current itself is the ladder
generator; the totient recursion `φ_{S∪p} = (p−1)φ_S` is its linearization at `x = 0`.

**R2 (repulsion–current locking; general k, paper proof).**  Let `Disc_S(x)` be the
discriminant of `P_S(·,x)`, `k = |S|`.  Then

```text
Disc_S(x) / J_S(x)^{k−1}  →  (−1)^{k(k−1)/2}·k^k     (x → 0⁺).
```

*Proof.*  Discriminants are translation-invariant, so compute at the parity jet
`P(−1+w) = ∑ e_j(x)w^j`; normalize `ĉ_j := e_j/e_k` (`e_k → 1`).  `Disc` is the universal
isobaric polynomial of weight `k(k−1)` in the `ĉ_j` (`ĉ_j` has weight `k−j`), every
`ĉ_j = O(x)` (T2), and a monomial with `m` factors contributes `O(x^m)`; weight `k(k−1)`
with factors of weight ≤ `k` forces `m ≥ k−1`, with equality **only** for `ĉ_0^{k−1}`.
Its coefficient is read off from `Disc(w^k + c_0) = (−1)^{k(k−1)/2} k^k c_0^{k−1}`, and
`ĉ_0 = J·(1+O(x))` with `J(x) = (−1)^{k+1}φ_S·x + O(x²)` (T2), so the remainder monomials
are `O(x^k) = o(J^{k−1})`.  ∎  (Checks: `k=2`: `Disc₂/J → −4`; `k=3`: `Δ/J² → −27`,
matching T3's `−27φ²x²`.)

Consequently `|Disc_S(x)| ≥ (k^k/2)·(φ_S x)^{k−1}` for small `x`: **yes**, the cluster
discriminants are lower-bounded inductively across the ladder, with constants driven by
R1.  Root-level reading: the `k`-star's pairwise separations `≍ x^{1/k}` never
degenerate faster than the current allows.

**R3 (the reversed rung).**  Because the leading repulsion invariant is a *pure power of
the current*, repulsion is not an independent rung: any lower bound on `|Disc|` is
equivalent to the trivial current asymptotics.  The (G2)-relevant direction is the
reverse inequality, which the locking law makes eventual and unconditional:

```text
J_S(x)² ≤ |Disc_S(x)|        (k = 3, all small x > 0),
```

i.e. **anomalous current cancellation can only come from anomalous cluster collapse** —
sub-`x^{k−1}` discriminant decay.  The graded route to (G2) is therefore: upper bounds on
the parity-cluster discriminant (partial vortex collapse), not repulsion lower bounds.
The singularity-theoretic content of R2 is an `A_{k−1}`-unfolding computation; the new
knowledge is the arithmetic identification (versal parameter = Möbius current, intensity
= totient, ladder = R1) and the direction-reversal R3 for the Route E seam programme.

- 2026-08-05 — R1–R3 proved on paper (this entry); Lean next: R1 (all `k`), the free
  degeneration, the `k = 2` and `k = 3` locking limits, and R3.

## 2026-08-05 R1–R3 FORMALIZED: `RHTower/GibbsClusterRepulsion.lean`

Wired into `RHTower.lean`; targeted build 8656 jobs; no `sorry`; axioms only
`propext, Classical.choice, Quot.sound`; zero warnings.  Namespace `RHTower.GibbsGas`:

- `gibbs_current_insert` (**R1**, all k, all x), `gibbsDiag_zero_parity` (free cluster
  degeneration `w^k`), `slope_limit_right` (reusable slope-limit bridge);
- `tendsto_pair_current_div` / `tendsto_triple_current_div` — the current slopes
  `−(p−1)(q−1)` and `+(p−1)(q−1)(r−1)` from the exported `hasDerivAt_gibbs_current`;
- `tendsto_pairDisc_div_current` (**R2, k=2**: `Disc₂/J → −4`),
  `tendsto_tripleDisc_div_sq_current` (**R2, k=3**: `Disc₃/J² → −27`) — the locking law,
  with `pairJet*/tripleJet*` jets, `gibbsDiag_pair_jet`/`gibbsDiag_triple_jet` tying the
  discriminants to the gas;
- `eventual_current_sq_le_abs_tripleDisc` (**R3**, the reversed rung `J² ≤ |Disc₃|`).

Lean traps: `Tendsto.div` produces the Pi-division `(f / g)` — `simp only [Pi.div_apply]`
before pointwise rewrites; `div_div_div_cancel_right₀` takes the nonzero proof FIRST
(`(hc) (a b)`); `field_simp` frequently closes the goal (trailing `ring` then errors);
prefer `rw [div_eq_iff ...]` over `field_simp` for value computations under `set`-bound
atoms.

- 2026-08-05 — R1–R3 formalized unconditionally.  General-k R2 remains paper-level (needs
  a general discriminant; mathlib has none — building it is a separate infrastructure
  decision).

## 2026-08-05 CYCLE 3: the sector-collapse layer

**N1 (infinite-volume gas is order-zero; paper proof).**  For fixed `x > 0`,
`p_x(z) := ∑_{n squarefree} z^{ω(n)}e^{−nx}` is entire of order `0`: its `k`-th
coefficient `c_k(x) = ∑_{ω(n)=k} μ²(n)e^{−nx}` obeys `c_k ≤ e^{−N_k x/2}·∑_n e^{−nx/2}`
with `N_k` the `k`-th primorial (`≥ 2^k·k!`-growth), so
`order = limsup k·log k / log(1/c_k) = 0`.  Hence the genus-`0` Hadamard factorization

```text
p_x(z) = e^{−x}·∏_j (1 − z/z_j(x)),      ∑_j |z_j(x)|^{−1} < ∞
```

(the constant term is `c_0 = e^{−x}`, the `n = 1` term).

**N2 (the parity cross-ratio law; paper proof).**  Evaluating at `z = ∓1` and dividing
(`p_x(1) > 0` by positivity):

```text
Φ(x) = e^{−x}∏_j (1 + 1/z_j),      E_{ν_x}[η] = Φ(x)/Z(x) = ∏_j (z_j+1)/(z_j−1).
```

A factor has modulus `< 1` **iff `Re z_j < 0`**, and a zero at distance `d` from the
parity point contributes `≈ log(2/d)` of cancellation.  Consequently **(G2)/RH is exactly
a zero-condensation law**: `∑_j log|(z_j−1)/(z_j+1)| ≥ (1/2−ε)·log(1/x)` — the
infinite-volume parity cluster must condense onto `z = −1` at logarithmic rate `1/2`.
This is the infinite-volume replacement of the locking law, and the precise meaning of
"anomalous cluster collapse" from R3.

**N3 (sector-collapse conjecture + finite theorems).**
*Conjecture (all k):* the gas is Hurwitz-stable — every zero of `P_S(·,x)` (and of `p_x`)
has `Re z < 0`, for every coupling `x > 0`.  Then every factor of N2 helps: cancellation
is **monotonically graded zero-by-zero**, and (G2) reduces purely to *counting* zeros
near the parity point.  Mechanism for an inductive proof: Hermite–Biehler along T0 —
`P_{S∪p}(iω) = P_S(iω,x) + iω·P_S(iω,px)` is a stability-preserving combination if the
two-scale phase lag is controlled; the Laplace kernel `e^{−xE}` is totally positive in
`(x,E)`, which is the structural reason to believe the lag control.  Hand-checks: the
`k=4` Routh–Hurwitz minors pass with room at both ends (`pqr+pq+p < min(2pqr+1,
pqrs+2p)`, both by `q+1 ≤ qr`-type submultiplicativity); the UV vortex star lies at
`−1 + O((φx)^{1/k})` ⊂ LHP.

*Theorems (k ≤ 3, ALL x > 0, proved):*  positivity of the coefficients plus the
Routh–Hurwitz energy inequality

```text
a₂a₁ ≥ e^{−(pq+p)x} > e^{−(pqr+1)x} = a₃a₀     (since p(q+1) ≤ pqr, strict in the exponent)
```

give: the pair gas and the triple gas have **no zero with `Re z ≥ 0`, at any coupling** —
the vortex never crosses the imaginary axis, even though reality fails (T3).  Proof of
the cubic criterion (classical Routh–Hurwitz, self-contained): a root `z = s+it` with
`s ≥ 0`; if `t = 0` then `P(s) ≥ a₀ > 0`; else the imaginary part forces
`a₃t² = 3a₃s² + 2a₂s + a₁`, and substituting into the real part yields
`a₂a₁ − a₃a₀ = −(8a₃²s³ + 8a₃a₂s² + 2a₃a₁s + 2a₂²s) ≤ 0`, contradiction.  Per-zero
grading: `Re ζ < 0 ⟹ ‖1+ζ‖ < ‖1−ζ‖` (difference of squares is `4·Re ζ`).

Attribution: the cubic criterion is Routh–Hurwitz (1895); new content = the gas satisfies
it at every coupling by energy submultiplicativity, the cross-ratio/condensation
reformulation N2, and the sector-collapse conjecture with the T0/Hermite–Biehler
mechanism.  `[OPEN CORE]` (refined): the zero-counting law — lower bounds on the number
of gas zeros in shrinking disks about the parity point; sector stability for `k ≥ 4` and
for `p_x`.

- 2026-08-05 — N1, N2 paper-proved; N3 finite theorems proved; Lean next
  (`RHTower/GibbsSectorStability.lean`).

## 2026-08-05 N3 FORMALIZED: `RHTower/GibbsSectorStability.lean`

Wired; targeted build 8657 jobs; no `sorry`; axioms only
`propext, Classical.choice, Quot.sound`; zero warnings.  Namespace `RHTower.GibbsGas`:

- `quadratic_no_rhp_root`, `cubic_no_rhp_root` — self-contained Routh–Hurwitz half-plane
  criteria (the cubic by the `s+it` substitution and the exact identity
  `a₂a₁ − a₃a₀ = −(8a₃²s³+8a₃a₂s²+2a₃a₁s+2a₂²s)` via
  `linear_combination (−a₃)·hre + (−(3a₃s+a₂))·hquad`);
- `gibbsDiag_pair_expand`, `gibbsDiag_triple_expand` — coefficient-basis bridges;
- `triple_gas_hurwitz` — the energy inequality `a₃a₀ < a₂a₁` at every coupling
  (submultiplicativity via `(q−2)(r−1) ≥ 0 ⟹ qr−q−1 ≥ 1`);
- `pair_gas_sector_stable`, **`triple_gas_sector_stable`** — no zero with `Re z ≥ 0`,
  for ALL `x > 0` (the vortex never crosses the imaginary axis);
- `norm_one_add_lt_of_re_neg`, **`triple_gas_root_grading`** — every zero of the triple
  gas, at every coupling, satisfies `‖1+ζ‖ < ‖1−ζ‖`: per-zero parity cancellation.

Lean traps: extract re/im of a complex root equation by `z = ↑s + ↑t·I` + `congrArg
Complex.re/im` + `simp only [add_re/mul_re/... , pow_succ, pow_zero, one_mul]` and close
against the hand-stated real equation with `linear_combination h` (immune to simp's
arrangement); `push_neg` is deprecated (use `rw [not_lt]`); nlinarith needs the
`(q−2)(r−1) ≥ 0`-style product hints spelled out.

- 2026-08-05 — N3 (k ≤ 3) formalized unconditionally.

## 2026-08-05 CYCLE 4: dilation seam, homotopy reduction, and k = 4 stability

**O1 (operator factorization; exact, all k).**  With `(M_c f)(x) := f(cx)`:

```text
P_S(z, x) = [ ∏_{p∈S} (1 + z·M_p) ] (e^{−·}) (x),
```

a product of COMMUTING operators (`M_pM_q = M_{pq}`).  T0 is the peeling of one factor.
At `z = −1` the parity current is the Möbius transfer product `∏(1−M_p)` applied to the
Gibbs state.

**O2 (the seam is the critical line; paper).**  On `L²(0,∞)`, `M_p = p^{−1/2}·U_p` with
`U_p` unitary (Mellin: `U_p` = multiplication by `p^{−iτ}`), so the commuting family
`{M_p}` is simultaneously diagonalized by Mellin with symbol `p^{−s}` on `Re s = 1/2`.
The exact scaling `‖M_p f‖² = p^{−1}‖f‖²` is the square-root-of-p law that seats the
gas seam on the critical line — unconditionally, before any zeta input.  (Honest flag:
pushing the z = −1 operator formula into L² approximation language lands in
Nyman–Beurling territory — a known re-encoding class per `rh-criterion-reencoding-template`;
the NEW content is the z-deformation: the gas polynomial and its zero geometry interpolate
the parity point.)

**O3 (homotopy reduction of all-k stability; paper).**  Zeros of `P_S(·,x)` move
continuously in `x`; therefore Hurwitz stability for all `x` follows from
(i) an anchor at one coupling and (ii) no zeros on the imaginary axis for any `x`.
- *Anchor (strong coupling)*: for large `x` the coefficient sequence
  `c_j(x) ≈ e^{−x·(p₁⋯p_j)}` satisfies Kurtz's dominance `c_j² > 4c_{j−1}c_{j+1}`
  (since `p_{j+1} + 1/p_j > 2` strictly), hence ALL roots are real negative (Kurtz 1992)
  — **Lee–Yang reality is restored at strong coupling**: the gas has a reality phase
  transition in `x` (vortex at weak coupling, real-rooted at strong coupling).
- *Axis nonvanishing*: `P_S(it, x) ≠ 0` for real `t` is exactly the Routh–Hurwitz minor
  chain for the gas coefficients.

**O4 (k = 4 minor at every coupling: the energy-injection theorem; paper proof).**
For `S = {p,q,r,s}` (distinct, ≥ 2), all `x > 0`:

```text
A₁A₂A₃ > A₀A₃² + A₁²A₄ .
```

*Proof (term injection; uniform in x because `u < v ⟹ e^{−xu} > e^{−xv}`).*
`A₁A₂A₃` is indexed by independent triples `(a, P, U)` (single, pair, triple ⊆ S).
- Map `A₀A₃²`-indices `(T, T')` to `(min T, T∖min T, T')`.  Energy drops strictly:
  `t₁ + t₂t₃ < 1 + t₁t₂t₃` ⟺ `(t₁−1)(t₂t₃−1) > 0`.  Range ⊆ `{a < min P}`; injective.
- Map `A₁²A₄`-indices `(a, a')` to `(a, {a', b}, S∖{b})` with `b := min(S∖{a'})`.
  Energy drops strictly: `a'b + E(S)/b < a' + E(S)` ⟺ `a' < ∏(S∖{b})`, true since
  `a' ∈ S∖{b}` and the other two factors are `≥ 2`.  Range ⊆ `{min P = min S ≤ a}`;
  injective (`b` = the pair element outside the triple).
The two ranges are disjoint (`a < min P` vs `a ≥ min P`), so the 32 strictly-dominating
LHS terms are distinct, and the remaining LHS terms are positive.  ∎

With the quartic Routh–Hurwitz criterion (positive coefficients + this minor), the
**4-element gas is Hurwitz-stable at every coupling** — N3 extends to `k = 4`, and the
energy-injection technique is the visible template for the full minor chain (the all-k
sector-collapse conjecture's likely proof engine).

Lean this cycle: the dilation layer (`GibbsDilationSeam.lean`): the semigroup law, the
operator form of T0, and the exact `p^{−1/2}` L²-scaling.  Next Lean targets: the quartic
Routh–Hurwitz criterion + the O4 injection (32 comparisons), then Kurtz's anchor.

- 2026-08-05 — O1–O4 established (O1, O3, O4 paper-proved here; O2's Mellin part cites
  classical Plancherel — corpus owns the machinery per `mathlib-has-plancherel`).

## 2026-08-05 O1 + scaling law FORMALIZED: `RHTower/GibbsDilationSeam.lean`

Wired; build 8657 jobs; no `sorry`; axioms clean; zero warnings.  `RHTower.GibbsGas`:
`dilate`, `dilate_dilate`/`dilate_comm` (the semigroup `M_pM_q = M_{pq}`),
`gibbsDiag_insert_dilate` (T0 = peeling one factor of `∏(1+z·dilate p)`),
`gibbsDiag_eq_sum_dilates` (the expanded operator product on the Gibbs state),
`integral_dilate_sq` (the exact `p⁻¹` squared-mass scaling —
`MeasureTheory.Measure.integral_comp_mul_left`; note the `Measure.` namespace).
Remaining Lean targets queued: quartic Routh–Hurwitz + the O4 injection; Kurtz anchor.

- 2026-08-05 — cycle 4 closed (O1–O4 paper; O1 + scaling law in Lean).

## 2026-08-05 O4 + QUARTIC CRITERION FORMALIZED: `RHTower/GibbsQuarticStability.lean`

Wired; build 8658 jobs; no `sorry`; axioms clean; zero warnings.  `RHTower.GibbsGas`:

- **`quartic_no_rhp_root`** — the quartic Routh–Hurwitz criterion, proved constructively
  by the conjugate-pair factorization: for a root `s+it`, `s ≥ 0`, the division identity
  `P = (z²−2sz+m)(a₄z²+bz+c) + r₁z + r₀` (a `ring` identity once `b := a₃+2sa₄`,
  `c := a₂+2sb−a₄m`, `r₁, r₀` are defined), `q(z₀) = 0` via `linear_combination
  t²·Complex.I_sq`, `r₁ = r₀ = 0` from re/im, and then the **exact identity**
  `a₃a₂a₁ − a₄a₁² − a₃²a₀ = −2sb·[(a₄m−c)² + a₃a₁]` (one `ring` after substituting the
  four relations) — so `Δ₃ > 0` forbids `s ≥ 0`.  No Cauchy index, no case analysis on
  root types, no interlacing machinery: the criterion reduced to two ring identities.
- `gibbsDiag_quadruple_expand` — the 16-term coefficient bridge (T0 applied 1+2+4+8 times);
- **`quadruple_gas_hurwitz`** — the O4 energy-injection minor `A₄A₁² + A₃²A₀ < A₃A₂A₁`
  at every coupling: the 8 strict comparisons via `exp_pair_lt` with product hints
  `(a−1)(bc−1) > 0`, aggregated by calc chains (`mul_lt_mul_of_pos_*`, `add_lt_add`)
  and closed by `ring` on the 96-monomial regrouping — no large simplex anywhere;
- **`quadruple_gas_sector_stable`**, **`quadruple_gas_root_grading`** — the 4-element gas
  never crosses the imaginary axis, and every zero contributes parity cancellation, at
  every coupling.

N3 now holds for `k ≤ 4` in Lean.  Lean traps: `set`-atom Boltzmann weights must be
`clear_value`d before arithmetic joints; big-product inequalities must be assembled by
`calc`/`add_lt_add`/`mul_le_mul` with `ring` regroupings — `linarith` over a 96-monomial
tableau exceeds 1.6M heartbeats, `ring` does it instantly.

- 2026-08-05 — quartic criterion + O4 formalized unconditionally; N3 ≤ 4 closed in Lean.

## 2026-08-05 CYCLE 6: weak-coupling confinement — the first ALL-k theorem

The Routh minor chain is bypassed.  All statements below hold for **every** `k`, are
unconditional, and use neither Rouché nor the fundamental theorem of algebra.

**W1 (perturbation estimate).**  For finite `S` of integers `≥ 1`, `x ≥ 0`, `w ∈ ℂ`:

```text
‖P_S(−1+w, x) − w^k‖ ≤ x·∏_{p∈S}(1 + (1+‖w‖)p) ≤ x·m·(2+‖w‖)^k,   m = ∏S.
```

*Proof.*  `∑_{T⊆S}(w−1)^{|T|} = w^k` exactly (binomial), so the difference is
`∑_T (w−1)^{|T|}(e^{−x·e(T)} − 1)`; then `|e^{−u}−1| ≤ u` and
`∑_T ∏_{p∈T}((1+‖w‖)p) = ∏_p(1+(1+‖w‖)p)`, with `1+(1+t)p ≤ (2+t)p` since `p ≥ 1`. ∎

**W2 (confinement, all k).**  If `ρ > 0` and `x·m < (ρ/(2+ρ))^k`, then `P_S(z,x) ≠ 0` for
every `z` with `‖z+1‖ ≥ ρ`: the entire zero set is confined to the open disk of radius `ρ`
about the parity point.
*Proof.*  `|P| ≥ ‖w‖^k − x·m(2+‖w‖)^k > 0` because `t ↦ t/(2+t)` increases. ∎

**W3 (weak-coupling Hurwitz stability, ALL k).**  `x·m < 3^{−k}` ⟹ every zero satisfies
`‖z+1‖ < 1`, hence `Re z < 0`.  The first all-`k` sector-stability theorem for the gas
(previous results: `k ≤ 4`, cycles 3–5).

**W4 (sharpness — the quantitative totient law).**  For `k ≥ 1` and `x·m ≤ 1`:

```text
|J_S(x) − (−1)^{k+1}·φ(m)·x| ≤ x²·∏_{p∈S}(1+p²).
```

So T2's totient law is now an inequality with explicit error, and the confinement radius
of W2 is **sharp**: the star of T4 has radius `(φ(m)x)^{1/k}`, W2 gives
`ρ ≤ 2(mx)^{1/k}`, and `(m/φ(m))^{1/k} = ∏(p/(p−1))^{1/k} = O(1)`.  **Cluster radius
pinned: `(φ(m)x)^{1/k} ≲ ρ_S(x) ≤ 2(mx)^{1/k}`.**

**W5 (quantitative grading).**  `‖1+ζ‖ ≤ ρ ⟹ ‖1−ζ‖ ≥ 2−ρ`: each confined zero contributes
a cancellation factor `≤ ρ/(2−ρ)`, so (with the finite factorization)
`|J_S|/Z_S ≤ (ρ/(2−ρ))^k` — matching W4's order `φ(m)x/2^k`.  The N2 condensation
mechanism is thereby verified quantitatively in finite volume, with no Hadamard theory.

Significance: the vortex picture becomes a quantitative confinement law valid for every
`k`.  Combined with the strong-coupling Kurtz anchor (O3), the only remaining unknown in
the sector-collapse conjecture is the **intermediate window** `3^{−k} ≤ x·m ≲ Kurtz`.

- 2026-08-05 — W1–W5 paper-proved (this entry); Lean next.

## 2026-08-05 W1–W5 FORMALIZED: `RHTower/GibbsWeakCouplingConfinement.lean`

Wired; build 8657 jobs; no `sorry`; axioms only `propext, Classical.choice, Quot.sound`;
zero warnings.  Namespace `RHTower.GibbsGas`:

- `gibbsDiagC` (the gas at complex activity), `gibbsDiagC_ofReal`;
- `sum_sub_one_pow_card` — the free gas `∑_{T⊆S}(w−1)^{|T|} = w^k` (`Finset.prod_add`);
- **`norm_gibbsDiagC_shift_sub_pow_le`** (W1) — `‖P_S(−1+w,x) − w^k‖ ≤ x·(2+‖w‖)^k·m`;
- **`gibbsDiagC_ne_zero_of_le_norm`** (W2) — confinement: `x·m < (ρ/(2+ρ))^k` ⟹ no zero
  with `‖z+1‖ ≥ ρ`, for EVERY `k`;
- **`gibbs_weak_coupling_stable`** (W3) — `x·m < 3^{−k}` ⟹ `‖z+1‖ < 1 ∧ Re z < 0`;
- `norm_one_sub_ge_of_norm_one_add_le` (W5) — `‖1+ζ‖ ≤ ρ ⟹ ‖1−ζ‖ ≥ 2−ρ`;
- **`abs_gibbs_current_sub_totient_le`** (W4) — `|J_S(x) − (−1)^{k+1}φ(m)x| ≤ x²∏(1+p²)`
  for `k ≥ 1`, `x·m ≤ 1` (sharpness certificate for the confinement radius).

Lean traps: `Finset.prod_add`'s cofactor `∏_{S∖T} 1` normalizes to `1 ^ card` — the simp
set needs `one_pow` (not `Finset.prod_const_one`); `Finset.prod_le_prod_of_subset_of_one_le'`
needs a multiplicative `OrderedCommMonoid` and does NOT apply to ℝ — split with
`Finset.prod_sdiff` and `nlinarith` instead; `Real.abs_exp_sub_one_sub_id_le` needs
`|u| ≤ 1` and gives constant `1`.

Stage: the gas programme now has ALL-k results (W1–W5) plus exact `k ≤ 4` stability at
every coupling.  Open: the **intermediate window** `3^{−k} ≤ x·m ≲ Kurtz` — the only
remaining gap in the sector-collapse conjecture.

- 2026-08-05 — cycle 6 closed.

## 2026-08-05 CYCLE 7: the recursive stability theorem (threshold `1/σ(m)`)

W3's threshold `x·m < 3^{−k}` is exponentially far from the natural barrier.  The T0
recursion removes the entire exponential loss — this is the Hermite–Biehler-along-T0
mechanism the programme predicted, in its correct (relative-error) form.

**V1 (exact error recursion).**  Put `E_S(z,x) := P_S(z,x) − (1+z)^{|S|}` (the deviation
of the gas from the free gas).  T0 gives, exactly,

```text
E_{S∪p}(z, x) = E_S(z, x) + z·E_S(z, px),      E_∅(z,x) = e^{−x} − 1.
```

**V2 (the relative estimate).**  On the region `1 ≤ ‖1+z‖` and `‖z‖ ≤ ‖1+z‖` — which
contains the whole closed right half-plane —

```text
‖P_S(z,x) − (1+z)^k‖ ≤ x·σ(m)·‖1+z‖^k,      σ(m) = ∏_{p∈S}(1+p).
```

*Proof.*  Induction along V1: `‖E_{S∪p}‖ ≤ ‖E_S(x)‖ + ‖z‖·‖E_S(px)‖ ≤ x·g_S·‖1+z‖^k·(1 +
p‖z‖)`, and `1 + p‖z‖ ≤ (1+p)‖1+z‖` because `1 ≤ ‖1+z‖` and `‖z‖ ≤ ‖1+z‖`; so
`g_{S∪p} = (1+p)g_S`, `g_∅ = 1`.  The factor `p` of the dilated scale `px` is exactly what
the geometry `1 + p‖z‖ ≤ (1+p)‖1+z‖` absorbs — no modulus is taken inside the product, so
no `2^k`/`3^k` is ever created. ∎

**V3 (Hurwitz stability, all k, threshold `1/σ(m)`).**  `x·σ(m) < 1` ⟹ the gas has no
zero with `Re z ≥ 0`.  Strictly stronger than W3 (`σ(m) ≤ 3^k·m`).

**V4 (localization dichotomy).**  Under `x·σ(m) < 1`, every zero satisfies
`‖z+1‖ < 1` **or** `Re z < −1/2`: the zero set splits into the parity cluster and a
far-left region, with the strip `{Re z ≥ −1/2} ∖ {‖z+1‖<1}` entirely free.

**Sharpness.**  The parity star of T4 reaches the unit circle at `x ≈ 1/φ(m)`, and
`σ(m)/φ(m) = ∏(p+1)/(p−1) ≍ (log p_k)²`: the threshold `1/σ(m)` is within a
**polylogarithmic** factor of the natural barrier, versus the exponential gap of W3.
Whether stability persists past `1/φ(m)` is the remaining window; it does for `k ≤ 4` at
every coupling (cycles 3–5).

- 2026-08-05 — V1–V4 paper-proved (this entry); Lean next.

## 2026-08-05 V1–V4 FORMALIZED: `RHTower/GibbsRecursiveStability.lean`

Wired; build 8658 jobs; no `sorry`; axioms only `propext, Classical.choice, Quot.sound`;
zero warnings; **one-iteration compile**.  Namespace `RHTower.GibbsGas`:

- `gibbsDiagC_empty`, **`gibbsDiagC_insert`** — the cutoff recursion at complex activity;
- `one_le_norm_one_add_of_re_nonneg`, `norm_le_norm_one_add_of_re` — the two geometric
  facts (`Re z ≥ 0 ⟹ 1 ≤ ‖1+z‖`; `Re z ≥ −1/2 ⟹ ‖z‖ ≤ ‖1+z‖`);
- **`norm_gibbsDiagC_sub_free_le`** (V2) — `‖P_S(z,x) − (1+z)^k‖ ≤ x·σ(m)·‖1+z‖^k`, by
  `Finset.induction_on` with `x` universally quantified inside the statement (the IH is
  applied at BOTH `x` and `p·x` — the two-scale step);
- **`gibbsDiagC_ne_zero_of_sigma`** (V3) — no zero with `Re z ≥ 0` when `x·σ(m) < 1`;
- **`gibbs_zero_localization`** (V4) — every zero is in `‖z+1‖ < 1` or has `Re z < −1/2`.

Note the hypothesis `∀ p ∈ S, 1 ≤ p` is NOT needed anywhere: the estimate holds for any
finite set of naturals, because `1 + p‖z‖ ≤ (1+p)‖1+z‖` only uses `p ≥ 0`.

Lean note: quantify `x` inside the statement (`∀ x, 0 ≤ x → …`) rather than as a theorem
argument, so `Finset.induction_on` produces an induction hypothesis usable at the dilated
scale; this is the formal counterpart of the two-scale recursion.

- 2026-08-05 — cycle 7 closed.  Stability threshold improved from `3^{−k}/m` (W3) to
  `1/σ(m)` (V3), i.e. from exponential to polylogarithmic distance from the barrier.

## 2026-08-05 CYCLE 8: the two-scale positivity engine, and an honest volume audit

### U1 (the reduction — the exact inductive engine)

If `P_{S∪p}(z,x) = P_S(z,x) + z·P_S(z,px) = 0` with `Re z ≥ 0`, then `A = −zB` for
`A = P_S(z,x)`, `B = P_S(z,px)`, so `A·conj B = −z·|B|²` and `Re(A·conj B) ≤ 0`.  Hence:

```text
TSP_S(x, px) :  Re[ P_S(z,x)·conj P_S(z,px) ] > 0  for all Re z ≥ 0
       ⟹  P_{S∪p} has no zero with Re z ≥ 0.
```

**All-k sector stability is therefore implied by a positivity of an explicit real
quadratic form** — no root-tracking, no Routh chain, no homotopy.  Expanding,

```text
Re[P_S(z,x)·conj P_S(z,px)] = Σ_{j,l} B_{j,l}·r^{j+l}·cos((j−l)θ),
B_{j,l} = Σ_{|T|=j,|U|=l} e^{−x(e(T)+p·e(U))},   z = r e^{iθ}, |θ| ≤ π/2.
```

Terms with `|j−l| ≤ 1` are automatically `≥ 0`; the whole content is that they dominate.
At `x = 0` the form is exactly `|1+z|^{2k} ≥ 0`, and as `x → ∞` it tends to `1`: the
criterion is correct at both ends, and the open problem is the middle — now a *finite,
term-by-term* combinatorial inequality rather than an analytic one.

**Ordering insight.**  For `k = 2` the boundary condition reduces to
`b₁b₂ + 2√(a₁a₂c₁c₂) ≥ a₁c₂ + a₂c₁`, whose energy comparison `p·x + p·y ≤ y + pq·x`
requires `p ≤ q`.  So the induction must **adjoin primes in decreasing order** (the new
prime smaller than every prime already present).  This is a genuine structural constraint
on the ladder, invisible before U1.

### U2 (honest volume audit — a limitation of cycles 6–7)

The stability thresholds are `x·σ(m) < 1`, i.e. `x ≲ 1/m`.  The **infinite-volume** gas at
coupling `x` involves all primes `p ≲ 1/x`, so its effective `m = ∏_{p≤1/x}p = e^{θ(1/x)}`
and `x·σ(m) ≫ 1` always.  **None of the finite-volume stability theorems reach the
infinite-volume regime**; closing that is the real frontier, and V3 covers only
`S = {p ≤ log(1/x)}`.  This is recorded as a limitation, not a gap in the proofs.

### U3 (dictionary — labelled as re-encoding, not progress)

By Selberg–Delange, `D_z(s) = Σ_{n sf} z^{ω(n)}n^{−s} = ∏(1+z p^{−s}) = ζ(s)^z G(z,s)`, so
`p_x(z) ~ x^{−1}(log 1/x)^{z−1}G(z,1)/Γ(z)`.  Since `1/Γ` vanishes at `z = −1,−2,…` and
`G(z,1)` at `z = −p`, the infinite-gas zeros approach `{−1,−2,…} ∪ {−p}` as `x → 0` — all
real negative.  Near the parity point, `G(−1,1) = ∏(1−1/p)(1−1/p)^{−1} = 1` and
`1/Γ(z) ≈ −(z+1)`, giving

```text
dist(nearest gas zero, −1)  ≈  |Φ(x)|·x·(log 1/x)²,
```

so RH ⟺ that distance is `≪ x^{1/2−ε}(log)²`: **the distinguished gas zero traces the
zeta zeros**, its motion in `log(1/x)` being almost-periodic with frequencies `γ` and
amplitude `x^{1/2}` exactly under RH.  Also: the Erdős–Kac profile (`c_j` Poisson with
mean `λ = loglog(1/x)`) yields only `(log 1/x)^{−2}` of cancellation, versus the `x^{1/2}`
RH needs — **quantifying how much of (G2) lies beyond the smooth profile**.  Per
`rh-criterion-reencoding-template` this is a dictionary, claimed as guidance only.

- 2026-08-05 — U1 proved (Lean next); U2, U3 recorded.  The OPEN CORE is now `TSP_S`.

## 2026-08-05 U1 FORMALIZED: `RHTower/GibbsTwoScalePositivity.lean`

Wired; build 8659 jobs; no `sorry`; axioms only `propext, Classical.choice, Quot.sound`;
zero warnings.  Namespace `RHTower.GibbsGas`:

- `TwoScalePositive S x y` — the engine's invariant, `0 < Re[P_S(z,x)·conj P_S(z,y)]` on
  `Re z ≥ 0`;
- **`gibbsDiagC_insert_ne_zero_of_twoScale`** (U1) — the reduction: `TSP_S(x, px)` ⟹ the
  extended gas has no zero with `Re z ≥ 0`.  Proof: `A = −zB` ⟹ `A·conj B = −z·normSq B`
  (`Complex.mul_conj`), whose real part is `−z.re·normSq B ≤ 0`;
- `re_mul_conj_affine` — the exact real part of an affine × conjugate-affine product;
- **`twoScalePositive_empty`**, **`twoScalePositive_singleton`** — the engine holds
  unconditionally at levels 0 and 1, at EVERY pair of scales (the singleton form is
  `a₁a₂ + (a₁b₂+a₂b₁)Re z + b₁b₂|z|²`, manifestly positive);
- **`twoScalePositive_of_sigma`** — the engine holds at every level in the weak-coupling
  regime `xσ + yσ + xσ·yσ < 1`, via the relative estimate of cycle 7 (so the criterion is
  non-vacuous for all `k`);
- `gibbsDiagC_pair_ne_zero` — pair-gas stability at every coupling, re-derived from the
  engine (consistency check against cycle 3).

The OPEN CORE is now the single statement `TwoScalePositive S x (p·x)` for all `S`, `p`,
`x` — a positivity of an explicit real quadratic form, replacing "all-k sector stability".

Lean traps: `|>.re` does not parse inside a theorem statement — parenthesise;
`simp [Complex.mul_re]` rewrites `↑(rexp t)` into `Complex.exp ↑t` (use
`simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]` + `ring`);
`-‖w‖ ≤ w.re` comes from `Complex.re_le_norm (-w)` + `Complex.neg_re` + `norm_neg`.

- 2026-08-05 — cycle 8 closed.

## 2026-08-05 CYCLE 9: level-2 two-scale positivity, and the reduced criterion

### X1 (the general criterion — TSP by weighted diagonal dominance)

Write `Re[P_S(z,x)·conj P_S(z,y)] = Σ_n r^n Σ_{d} D_d^{(n)} cos(dθ)` (`z = re^{iθ}`,
`|θ| ≤ π/2`), where `D_d^{(n)} = B_{(n+d)/2,(n−d)/2} + B_{(n−d)/2,(n+d)/2}` for `d ≥ 1`
and `D_0^{(n)} = B_{n/2,n/2}`.  Using `cos(dθ) ≥ −1` for even `d`, and — the useful point —
**`|cos(dθ)| ≤ d·cos θ` for odd `d`** (equivalently `|sin(dφ)| ≤ d|sin φ|`), each group is
non-negative as soon as

```text
even n :  D_0 ≥ Σ_{d ≥ 2 even} D_d ;      odd n :  D_1 ≥ Σ_{d ≥ 3 odd} d·D_d .
```

So **all-k sector stability follows from an explicit finite inequality on Boltzmann sums**
— no analysis in `z` remains.  This is the reduced OPEN CORE.

### X2 (level two, proved — the decreasing-order condition is an identity)

For `S = {q,r}` the gas is `a + bz + cz²` with `a = e^{−x}`, `b = e^{−rx}+e^{−qx}`,
`c = e^{−qrx}`, and the criterion collapses to the single inequality
`b₁b₂ ≥ a₁c₂ + a₂c₁`.  With the **cross** pairing (not the diagonal one, which fails):

```text
e^{−qx}·e^{−ry} ≥ e^{−y}·e^{−qrx}   ⟺   q + rp ≤ p + qr   ⟺   (q−p)(r−1) ≥ 0,
e^{−rx}·e^{−qy} ≥ e^{−x}·e^{−qry}   ⟺   r + qp ≤ 1 + qrp   ⟺   (r−1)(qp−1) ≥ 0,
```

both automatic once `p ≤ q` and `p,q,r ≥ 1` (`y = px`).  **The decreasing-order constraint
discovered in cycle 8 is exactly the factor `(q−p)` in the first identity.**  Feeding this
to the engine re-proves stability of the three-element gas at every coupling — by a route
that generalizes, unlike the Routh computation of cycle 3.

Cartesian form used (no polar coordinates needed): with `Re z² = z.re²−z.im²`,

```text
(a₁c₂+a₂c₁)(z.re²−z.im²) + b₁b₂(z.re²+z.im²) ≥ 2(a₁c₂+a₂c₁)·z.re² ≥ 0,
```

and every other term of `Re[F·conj G]` is non-negative for `Re z ≥ 0`.

- 2026-08-05 — X1 stated (reduced open core), X2 proved; Lean next.

## 2026-08-05 X1/X2 FORMALIZED: `RHTower/GibbsTwoScaleLevelTwo.lean`

Wired; module build 8660 jobs; **whole `GaloisForLFunctions.RHTower` umbrella rebuilt
clean (16955 jobs)**; no `sorry`; axioms only `propext, Classical.choice, Quot.sound`;
zero warnings.  Namespace `RHTower.GibbsGas`:

- `re_mul_conj_quadratic` — the exact Cartesian expansion of `Re[F·conj G]` for
  quadratics (no polar coordinates);
- **`re_mul_conj_quadratic_pos`** — the level-two criterion: positive coefficients plus
  `a₁c₂ + a₂c₁ ≤ b₁b₂` give positivity on `Re z ≥ 0` (the only sign-indefinite term,
  `(a₁c₂+a₂c₁)(z.re²−z.im²)`, is absorbed by `b₁b₂(z.re²+z.im²)` leaving `2(a₁c₂+a₂c₁)z.re²`);
- `gibbsDiagC_pair_quadratic`, `exp_pair_le_of_le`;
- **`twoScalePositive_pair`** (X2) — the engine at level two, with the two crosswise
  energy comparisons closed by `nlinarith` from the factorizations `(q−p)(r−1) ≥ 0` and
  `(r−1)(qp−1) ≥ 0`;
- **`gibbsDiagC_triple_ne_zero`** — three-element gas stable at every coupling, now
  derived through the engine rather than by the Routh cubic of cycle 3.

Note on the repository lint gate: it currently reports orphan-module errors inside
`GaloisForLFunctions.HTGeometry` (`HalfLineTransportDistance`,
`SiteFactorLiftedSpectrum`, …), which come from concurrent work in that area and are
**not** from this programme — the set of reported orphans changed between two consecutive
runs while `HTGeometry.lean` was being edited elsewhere.  Nothing in `RHTower` is
implicated; the umbrella builds clean.

- 2026-08-05 — cycle 9 closed.  OPEN CORE: the X1 criterion (weighted diagonal dominance)
  at level `≥ 3`, i.e. `D_0 ≥ Σ_{d≥2 even}D_d` and `D_1 ≥ Σ_{d≥3 odd} d·D_d`.

## 2026-08-06 CYCLE 10: X1 falsified for k ≥ 5, and the condensation law made rigorous

### Y1 (NO-GO: the X1 criterion is empty beyond k = 4)

X1 uses `cos(dθ) ≥ −1`, which is lossy.  Test it at `x = 0`, where `B_{j,l} = C(k,j)C(k,l)`
and the true form is the perfect square `|1+z|^{2k} > 0`:

```text
k = 4, n = 4 :  D_0 = C(4,2)² = 36  ≥  32 + 2 = 34    ✓
k = 5, n = 4 :  D_0 = C(5,2)² = 100 <  100 + 10 = 110  ✗
k = 6, n = 6 :  D_0 = C(6,3)² = 400 <  2·C(6,4)C(6,2) = 450  ✗
```

and asymptotically `Σ_{j} C(k,j)C(k,n−j) = C(2k,n)`, so at `n = k` the off-diagonal mass
exceeds the diagonal by a factor `≍ √k`.  **X1 holds exactly for `k ≤ 4` — precisely the
range already covered — so it buys nothing.**  Any workable criterion must keep the phase
cancellation among the `cos(dθ)` terms (at `x = 0` they conspire into a perfect square);
bounding them termwise is fatal.  Recorded so no future cycle re-attempts it.

### Y2 (the finite-volume condensation law, now a theorem)

The gas is a polynomial of exact degree `|S|` with leading coefficient `e^{−x·m} ≠ 0`, so
over `ℂ` it factors completely.  Evaluating at the parity activity `z = −1` and at `z = 1`:

```text
‖J_S(x)‖ · ∏_ζ ‖1 − ζ‖  =  ‖Z_S(x)‖ · ∏_ζ ‖1 + ζ‖        (over the zeros, with multiplicity)
```

**The parity current is exactly the cross-ratio product of the gas zeros against the parity
point, at every coupling** — N2 in finite volume, with no Hadamard theory and no
smallness hypothesis.  This is the machine the programme was built to feed: any control of
zero locations transfers directly to the current.  First payoff (completing W5, which was
paper-level pending factorization): if every zero lies within `ρ` of the parity point,

```text
‖J_S(x)‖ · (2 − ρ)^{|S|}  ≤  ‖Z_S(x)‖ · ρ^{|S|}.
```

- 2026-08-06 — Y1 (no-go) and Y2 established; Lean below.

## 2026-08-06 Y2 FORMALIZED: `RHTower/GibbsParityFactorization.lean`

Wired; build 8658 jobs; no `sorry`; axioms only `propext, Classical.choice, Quot.sound`;
zero warnings.  `RHTower.GibbsGas`: `gibbsPoly` (the gas as `Polynomial ℂ`),
`gibbsPoly_eval`, `gibbsPoly_coeff`, `gibbsPoly_coeff_card`, **`gibbsPoly_natDegree`**
(= `|S|`, via `Finset.eq_of_subset_of_card_le` to isolate `T = S`), `gibbsPoly_ne_zero`,
`norm_multiset_prod_complex`, **`gibbsDiagC_eq_prod_roots`**, **`gibbs_roots_card`**,
**`gibbs_parity_cross_ratio`** (Y2), `prod_norm_one_add_le`, `pow_le_prod_norm_one_sub`,
**`norm_gibbs_current_le_of_confinement`**.

Lean traps: `Polynomial.Splits` is now **unary** (`p.Splits`, no ring hom) and the
factorization is `Polynomial.Splits.eq_prod_roots`; `IsAlgClosed.splits p` supplies it;
`(Polynomial.mem_roots h).mp` returns the root equation directly (no `.2`);
`Polynomial.eval_finset_sum`/`finset_sum_coeff` are deprecated in favour of
`eval_finsetSum`/`finsetSum_coeff`; `coeff_X_pow` orients its `if` as `j = T.card` while
`Finset.sum_filter` orients its own as `T.card = j` — rewrite both explicitly with
`if_pos h.symm` / `if_neg (fun hh => h hh.symm)`.

## 2026-08-06 CYCLE 11: THE ALL-k SECTOR-STABILITY CONJECTURE IS FALSE

The conjecture pursued since cycle 3 ("the gas has no zero with `Re z ≥ 0`, for every finite
`S` and every coupling") is **false**.  Counterexample family, with the mechanism:

**Z1 (truncation).**  If every `T` with `|T| ≤ J` is light (`x·e(T) ≤ ε`) and every larger
one heavy (`x·e(T) ≥ R`), then uniformly

```text
‖P_S(z,x) − Σ_{j≤J} C(k,j) z^j‖ ≤ (ε + e^{−R})·(1+‖z‖)^k.
```

**Z2 (the section limit).**  Take `S` = `k` primes in `[N, 2N]` and `x = N^{−(J+1/2)}`.
Then `ε = 2^J N^{−1/2} → 0` and `R = N^{1/2} → ∞`, so the gas is uniformly close to
`Σ_{j≤J}C(k,j)z^j`; substituting `z = w/k` and letting `k → ∞` (there are `≍ N/log N` primes
available) gives `C(k,j)/k^j → 1/j!`, i.e. the `J`-th Taylor section of the exponential,

```text
s_J(w) = Σ_{j≤J} w^j/j!.
```

The tail is harmless on the relevant scale `|z| ≍ J/k`, where `(1+‖z‖)^k = O(e^J)`.

**Z3 (the sixth section is unstable).**  For `q(w) = 6!·s₆(w) =
w⁶+6w⁵+30w⁴+120w³+360w²+720w+720`:

* `q(iy)` has imaginary part `6y((y²−10)² + 20)`, which vanishes only at `y = 0`, where
  `q(0) = 720 ≠ 0`: **no zeros on the imaginary axis**;
* its third Hurwitz determinant is `det [6,120,720; 1,30,360; 0,6,120] = −1440 < 0`, so by
  the necessity half of Routh–Hurwitz (Hurwitz 1895 — the one classical input here) `q` is
  not Hurwitz stable.

Together: `s₆` has a zero with `Re w > 0`.  (Independent confirmation: for a stable degree-6
real polynomial the even part of `q(iy)` must have three positive roots in `y²`; here
`u³−30u²+360u−720` has derivative `3(u²−20u+120) > 0`, so it is strictly increasing and has
exactly one.)  This is the finite-`J` shadow of Szegő's theorem: the zeros of `s_n(nz)`
accumulate on `|z e^{1−z}| = 1`, which meets `Re z > 0`.

**Z4 (conclusion).**  With `J = 6` and `k, N` large, the gas has a zero with `Re z > 0`.
**Sector stability fails**, so parity cancellation is *not* monotonically graded by the
zeros in general: some zeros contribute `‖1+ζ‖/‖1−ζ‖ > 1`, i.e. anti-cancellation.  The
cycle 3–9 stability results are therefore sharp in scope — `k ≤ 4` at all couplings, all `k`
at weak coupling — and the two-scale positivity `TSP` of cycle 8, being *sufficient* for
stability, must also fail in general.  **The engine cannot be completed; this closes that
line.**

What survives, and is now the load-bearing structure: the **condensation law** (cycle 10),
which is an identity valid at every coupling regardless of where the zeros sit.

- 2026-08-06 — conjecture falsified; Z1, Z3 formalized below.

## 2026-08-06 Z1/Z3 FORMALIZED: `RHTower/GibbsTruncationSection.lean`

Wired; build 8658 jobs; no `sorry`; axioms only `propext, Classical.choice, Quot.sound`;
zero warnings.  `RHTower.GibbsGas`: `sum_powerset_pow_card`,
`sum_powerset_card_le_eq_binomial` (light part = truncated binomial, via
`Finset.sum_fiberwise_of_maps_to` and `Finset.card_powersetCard`),
**`gibbsDiagC_sub_truncated_le`** (Z1), `expSection6`, `expSection6_axis`,
**`expSection6_ne_zero_on_axis`** (Z3, first half), **`expSection6_hurwitzDelta3`**
(Z3, second half: the minor equals `−1440`).

The only step not formalized is the classical necessity half of Routh–Hurwitz, which is
cited, not assumed: no Lean theorem here depends on it.

Lean trap: in `mul_le_mul_of_nonneg_left h (by positivity)` the multiplier is a
metavariable at elaboration time and `positivity` may unify it with the wrong hypothesis
(here `hx : 0 ≤ x`); bind it first with an explicit `have` and use a `calc`.

## 2026-08-06 CYCLE 12: scoping the falsification — energy spread blocks the mechanism

Cycle 11's counterexample used primes in a dyadic window `[N,2N]`, i.e. an
**energy-degenerate** set.  That is not an accident of the construction but a requirement.

**S1 (the dichotomy obstruction).**  The truncation lemma needs every `J`-configuration
light and every `(J+1)`-configuration heavy, so it forces

```text
max_{|T| = J} e(T)  <  min_{|T| = J+1} e(T)
```

— energies ordered by cardinality alone.  Exhibiting one `(J+1)`-set no heavier than some
`J`-set refutes it outright: `R ≤ x·e(T₂) ≤ x·e(T₁) ≤ ε < R`.

**S2 (the natural gas is never in the regime).**  For `S` = primes up to `y`, level `J`
would need the product of the `J` largest primes below the `(J+1)`-st primorial — false for
every `y` past a fixed bound, since the left side grows like `y^J` and the right side is a
constant.  Already `{2,3,7} ⊆ S` blocks level one: `2·3 ≤ 7`.

**Consequence — the refined conjecture.**  Cycle 11 falsifies sector stability for
*general* `S`; it says nothing about the arithmetically natural gas.  The structural
dichotomy behind this:

```text
sharp truncation of the coefficient profile  ⟹  Szegő regime  ⟹  right half-plane zeros,
gradual (super-exponentially decaying) profile ⟹ Kurtz regime ⟹ real negative zeros.
```

A dyadic window produces the first; the natural prime gas, whose energies span many
scales, produces the second (its coefficient profile is Poisson-like in the bulk with a
super-exponentially thin primorial tail).  **Refined conjecture: the natural gas
`S = {p prime : p ≤ y}` is sector-stable at every coupling.**  This — not the general
statement — is the Route E-relevant question, and it is now the sharp open core.

- 2026-08-06 — S1, S2 proved; refined conjecture stated.

## 2026-08-06 S1/S2 FORMALIZED: `RHTower/GibbsEnergySpread.lean`

Wired; build 8659 jobs; no `sorry`; axioms only `propext, Classical.choice, Quot.sound`;
zero warnings.  `RHTower.GibbsGas`: **`no_truncation_dichotomy`** (S1, general witness
form), **`no_truncation_dichotomy_of_dominant`** (a single element dominating a product of
two blocks level one), **`no_truncation_dichotomy_of_two_three_seven`** (the concrete
arithmetic instance `2·3 ≤ 7`).

## 2026-08-06 CYCLE 13: the condensation law becomes two-sided

Cycle 10 gave the identity in cross-ratio form.  Evaluating the same factorization directly
at the parity activity gives the sharper pair (`m = ∏ S`, product over zeros with
multiplicity):

```text
‖J_S(x)‖ = e^{−x·m} · ∏_ζ ‖1 + ζ‖ ,        ‖Z_S(x)‖ = e^{−x·m} · ∏_ζ ‖1 − ζ‖ .
```

**T1 (gap ⟹ current lower bound).**  If no zero comes within `δ` of the parity point,

```text
‖J_S(x)‖ ≥ e^{−x·m}·δ^{|S|}.
```

**T2 (the contrapositive — cancellation forces condensation).**  If
`‖J_S(x)‖ < e^{−x·m}·δ^{|S|}` then **some gas zero lies within `δ` of the parity point**.

Both hold at every coupling, for every finite `S`, with **no stability hypothesis** — which
matters now that sector stability is known to fail in general (cycle 11).  This is the
converse the programme was missing: cycle 10 showed confinement ⟹ cancellation, and T2
shows cancellation ⟹ confinement, with matching explicit rates.  Consistency check against
the weak-coupling laws: `‖J_S‖ ≈ φ(m)x` (W4) forces `δ ≲ (φ(m)x·e^{x m})^{1/k}`, matching
the confinement radius `2(mx)^{1/k}` of W2 up to constants.

Read arithmetically: **to make the Möbius–Laplace current anomalously small one must drag a
zero of the squarefree Gibbs gas onto the parity point, at an explicitly quantified rate.**
No mechanism can produce cancellation without producing condensation.

- 2026-08-06 — T1, T2 proved and formalized.

## 2026-08-06 T1/T2 FORMALIZED: `RHTower/GibbsCurrentGap.lean`

Wired; build 8659 jobs; no `sorry`; axioms only `propext, Classical.choice, Quot.sound`;
zero warnings.  `RHTower.GibbsGas`: `gibbsPoly_leadingCoeff`, `pow_le_prod_of_le`,
**`norm_gibbs_current_eq`**, **`norm_gibbs_current_ge_of_gap`** (T1),
**`exists_zero_near_parity_of_small_current`** (T2), `norm_gibbs_partition_eq`.

## 2026-08-06 CYCLE 14: distant zeros are inert — the dictionary closes

**U1 (per-zero localization).**  `‖1−ζ‖ ≤ 2 + ‖1+ζ‖`, so a zero at distance `d` from the
parity point contributes a cross-ratio at most `1 + 2/d`.  **Distant zeros are inert**: all
cancellation is produced by zeros near the parity point.  Division-free form, at every
coupling, no stability hypothesis:

```text
‖Z_S(x)‖ · ∏_ζ ‖1+ζ‖  ≤  ‖J_S(x)‖ · ∏_ζ (2 + ‖1+ζ‖).
```

With cycle 13 this closes the dictionary in both directions and with matching rates:

```text
gap δ around −1        ⟹  ‖J_S‖ ≥ e^{−xm}·δ^{|S|}                    (T1)
‖J_S‖ small            ⟹  a zero within δ of −1                      (T2)
zeros far from −1      ⟹  no cancellation (each contributes ≤ 1+2/d) (U1)
zeros confined to ρ    ⟹  cancellation ≤ (ρ/(2−ρ))^{|S|}             (cycle 10)
```

### Assessment of the refined conjecture (cycle 12) — likely also false

Honest prediction, recorded so no cycle chases it blindly.  For the natural gas the
coefficient profile is `A_j ≈ Z·λ^j/j!` with `λ = loglog(1/x)` throughout the Sathe–Selberg
range, and this persists (in large-deviation form) up to `j ≈ K`, where `K` is fixed by
`P_K x ≈ 1` (`P_K` the primorial); beyond `K` the profile drops super-exponentially because
the *minimum* energy `P_j` takes over.  That is a Poisson profile with a **sharp** cutoff,
i.e. `Z·e^{−λ}·s_K(λz)` — exactly the Szegő shape.  Since `s_K` has right half-plane zeros
for `K ≥ 6`, and `K ≥ 6` already for `x ≤ 1/30030`, the natural gas is probably unstable
too, and the refined conjecture false.

The obstruction to *proving* it is precise and worth stating: one needs Sathe–Selberg
counting uniform in `j` up to `j = K ≈ log(1/x)/loglog(1/x)`, far outside the usual
`j ≍ loglog` range.  That is a genuine analytic-number-theory input, not a gap in the gas
theory.  **Conclusion for the programme: stability is not the right structure to chase.
The two-sided condensation law is, and it needs no stability at all.**

- 2026-08-06 — U1 proved and formalized; refined conjecture downgraded to "likely false,
  with a named obstruction".

## 2026-08-06 U1 FORMALIZED: `RHTower/GibbsZeroLocalization.lean`

Wired; build 8660 jobs; no `sorry`; axioms only `propext, Classical.choice, Quot.sound`;
zero warnings.  `RHTower.GibbsGas`: `multiset_prod_map_le`, `norm_one_sub_le_two_add`,
**`gibbs_partition_le_current_mul_localization`**.

Repo note: this tree currently has several concurrent sessions writing to it (HTGeometry
umbrella churn, a `2-fully-proven` card, `RHTower/DivisorReesDehomogenization.lean`).  A
`pgrep -f "lean --"` check matches *their* shell command text and reports false "stale
process" hits; check `ps -Ao comm | grep -E "/lean$|/lake$"` instead.

## 2026-08-06 CYCLE 15: the arithmetic anchor — the gas IS the Möbius–Laplace current

Fourteen cycles proved theorems about "the parity point of the gas".  That the parity point
*is* Möbius was an interpretive claim on this card, not a Lean theorem.  It is now a
theorem.  For a finite set `S` of distinct **primes** with `m = ∏S`:

```text
gibbsDiag S x (−1)  =  ∑_{d ∣ m} μ(d)·e^{−d x}.
```

Ingredients: a product of distinct primes is squarefree; it has exactly `|T|` prime factors
with multiplicity; hence `μ(∏T) = (−1)^{|T|}` — the gas's alternating sign *is* the Möbius
function.  The re-indexing is the bijection `T ↦ ∏T` between `S.powerset` and the divisors
of `m`, inverted by `d ↦ d.primeFactors` (using `Nat.primeFactors_prod` and
`Nat.prod_primeFactors_of_squarefree`).

**Consequence.**  Every theorem of cycles 1–14 about the parity point is now, without
reinterpretation, a theorem about finite Möbius–Laplace sums.  In particular the two-sided
condensation law reads:

```text
|∑_{d∣m} μ(d)e^{−dx}| = e^{−x m}·∏_ζ ‖1+ζ‖ ,
```

so a Möbius–Laplace sum is anomalously small **iff** a zero of the associated gas polynomial
condenses onto `−1`, at the explicit rate of T1/T2.

- 2026-08-06 — arithmetic anchor established.

## 2026-08-06 CYCLE 15 FORMALIZED: `RHTower/GibbsMoebiusAnchor.lean`

Wired; build 8656 jobs; no `sorry`; axioms only `propext, Classical.choice, Quot.sound`;
zero warnings.  `RHTower.GibbsGas`: `squarefree_prod_primes`, `cardFactors_prod_primes`,
**`moebius_prod_primes`**, **`gibbs_parity_eq_moebius_powerset`**,
**`gibbs_parity_eq_moebius_divisors`**.

Also re-verified after concurrent edits by other sessions in this tree: the full
`GaloisForLFunctions.RHTower` umbrella rebuilds clean (17094 jobs).

Lean notes: the `μ` notation needs `open scoped ArithmeticFunction.Moebius` — with plain
`open ArithmeticFunction` write `moebius`, else `autoImplicit` silently binds `μ` as a
variable and the error is confusing; `Finset.sum_nbij'` wants the two maps, two membership
proofs, two inverse proofs and the value equality, in that order.

## 2026-08-06 CYCLE 16: the infinite-volume bridge (U2 closed)

The limitation recorded as **U2** in cycle 8 — "the finite theory does not reach the
infinite-volume object" — is now closed as a theorem.  Define the genuine Möbius–Laplace
transform `Φ(x) = ∑'_n μ(n)e^{−nx}`.  For every `x > 0` and every cutoff `y`:

```text
|Φ(x) − P_{S_y}(−1, x)|  ≤  e^{−(y+1)x} / (1 − e^{−x}),      S_y = {p prime : p ≤ y}.
```

*Proof.*  By the cycle-15 anchor the gas over `S_y` is `∑_{d ∣ m} μ(d)e^{−dx}`, and the
divisors of `m = ∏S_y` are exactly the squarefree integers all of whose prime factors are
`≤ y`.  Any `n` missing from that list with `μ(n) ≠ 0` is squarefree with a prime factor
above `y`, hence `n > y` — because a squarefree `n ≤ y` has all its prime factors `≤ n ≤ y`
and therefore divides the primorial.  The difference is thus supported beyond `y` and is
dominated termwise by the geometric tail `∑_{n>y} e^{−nx}`. ∎

Consequences: every finite-volume statement of cycles 1–15 transfers to `Φ` with an
exponentially small, fully explicit error.  Choosing `y ≍ C·log(1/x)/x` makes the error
`O(x^C)`, far below any power relevant to (G2).  In particular the two-sided condensation
law now constrains the true Möbius–Laplace transform, not just its truncations.

- 2026-08-06 — U2 closed.

## 2026-08-06 CYCLE 16 FORMALIZED: `RHTower/GibbsInfiniteVolume.lean`

Wired; build 8657 jobs; no `sorry`; axioms only `propext, Classical.choice, Quot.sound`;
zero warnings.  `RHTower.GibbsGas`: `moebiusLaplace`, `primesUpTo`, `exp_neg_mul_nat`
(Boltzmann weights are powers of `e^{−x}`), **`dvd_prod_primesUpTo`**,
**`abs_moebiusLaplace_sub_gibbs_le`**.

Lean notes: `set F : ℕ → ℝ := fun n => …` makes `rw [hF]` fail on applied occurrences —
use `simp only [hF]` (it beta-reduces).  For `|∑' g| ≤ ∑' h` avoid the norm route
(`norm_tsum_le_tsum_norm` triggered `whnf` timeouts here); sandwich instead with
`Summable.tsum_le_tsum` applied twice, using `−h ≤ g ≤ h` and `tsum_neg`.  The finite part
is best obtained from `hasSum_sum_of_ne_finset_zero`, which gives both the summability and
the `tsum = Finset.sum` identity.

## 2026-08-06 CYCLE 17: the capstone — cancellation ≤ Coulomb potential of the zeros

Taking logarithms in the localization inequality converts the product over zeros into a
sum, which is the form that survives a large zero set: inert zeros contribute essentially
nothing.  With `d_ζ = ‖1+ζ‖` the distance of a zero to the parity point, and provided the
current does not vanish,

```text
log ‖Z_S(x)‖ − log ‖J_S(x)‖  ≤  ∑_ζ 2 / d_ζ .
```

**The logarithmic cancellation of a Möbius–Laplace sum never exceeds twice the Coulomb
potential of the gas zeros at the parity point.**  Unlike T1/T2 this statement is
non-vacuous however large the prime set is, because the sum weights each zero by its own
proximity: adding primes far beyond the coupling scale adds zeros of distance `≫ 1`, which
contribute `≈ 0`.

Combined with cycles 15–16 this is the programme's sharpest form.  For the true transform,
`Z(x) ≍ 1/x`, so an RH-strength bound `|Φ(x)| ≪ x^{−1/2−ε}` forces

```text
∑_ζ 1 / d_ζ  ≥  (1/4 − o(1))·log(1/x) :
```

**RH requires the zeros of the squarefree Gibbs gas to accumulate at the parity point with
Coulomb potential growing like `log(1/x)`.**  This is a necessary condition, stated
unconditionally and quantitatively; it is the precise sense in which parity cancellation
*is* zero condensation.

- 2026-08-06 — capstone proved and formalized.

## 2026-08-06 CYCLE 17 FORMALIZED: `RHTower/GibbsPotentialBound.lean`

Wired; build 8661 jobs; no `sorry`; axioms only `propext, Classical.choice, Quot.sound`;
zero warnings.  `RHTower.GibbsGas`: `multiset_log_prod`, `multiset_sum_map_le`,
`multiset_sum_map_add`, `gibbsDiagC_one_ne_zero` (the partition function is a positive
real), `norm_one_add_pos_of_root`, **`log_partition_sub_log_current_le`**.

Lean note: the termwise step is `log((2+d)/d) ≤ (2+d)/d − 1 = 2/d`
(`Real.log_le_sub_one_of_pos`), so no series expansion of `log(1+u)` is needed.

## 2026-08-06 CYCLE 18: the capstone sharpened to an EXACT identity

The cycle-17 bound is one reading of an equality.  Both product formulas of cycle 13 have
the same prefactor `e^{−xm}`, so it cancels in the ratio and — with no zero at `±1`, i.e.
whenever the current is nonzero —

```text
log ‖Z_S(x)‖ − log ‖J_S(x)‖  =  ∑_ζ ( log‖1−ζ‖ − log‖1+ζ‖ ) .
```

**The logarithmic cancellation of a Möbius–Laplace sum is exactly the sum of logarithmic
cross-ratios of the gas zeros against the parity point.**  No estimate, no hypothesis on
the zero locations, every coupling.  The necessary direction (cycle 17, Coulomb potential)
and the sufficient direction (cycles 10 and 13) are both readings of this one identity,
obtained by bounding its summands from either side.

With the anchor (cycle 15) and the bridge (cycle 16), the (G2)/RH statement becomes an
exact statement about a zero set:

```text
RH   ⟺   ∑_ζ log( ‖1−ζ‖ / ‖1+ζ‖ )  ≥  (1/2 − ε)·log(1/x)     (up to the explicit tail).
```

Every summand is positive exactly when the zero lies in the open left half-plane, which is
why the stability programme mattered — and why its failure (cycle 11) matters: some
summands can be negative, and the identity accounts for them exactly.

- 2026-08-06 — exact form proved and formalized (`log_cancellation_eq`), build 8661 jobs,
  no `sorry`, axioms clean.  Added `norm_one_sub_pos_of_root`.

Lean note: keep multiset maps in plain lambda form throughout — after `multiset_log_prod`
normalize with `simp only [Multiset.map_map, Function.comp_def]` rather than
`Multiset.map_map` alone, otherwise `Real.log ∘ f` and `fun ζ => Real.log (f ζ)` become
distinct atoms and `linarith`/`ring` cannot match them.

## 2026-08-06 CYCLE 19: the zero potential IS an arithmetic ratio

Eighteen cycles produced geometry constrained by arithmetic.  This one closes the loop in
the other direction.  The logarithmic derivative of the gas at the parity point is, on one
side, the Coulomb sum of the zeros against that point and, on the other, an explicit ratio
of Möbius-weighted Laplace sums — the numerator weighted by the number of prime factors.
For `J_S(x) = P_S(-1,x) ≠ 0`:

```text
∑_ζ 1/(1+ζ)  =  ( ∑_{T ⊆ S} |T|·(−1)^{|T|}·e^{−x·e(T)} ) / J_S(x)
             =  ( ∑_{d ∣ m} μ(d)·ω(d)·e^{−d x} ) / ( ∑_{d ∣ m} μ(d)·e^{−d x} ),
```

the second line by the cycle-15 anchor (`ω(d) = |T|` on squarefree divisors).  **At the
parity point the zero potential is not merely bounded by arithmetic — it *is* an arithmetic
ratio.**  With cycle 17 (`log ‖Z‖ − log ‖J‖ ≤ ∑ 2/‖1+ζ‖`) and
`∑_ζ 1/‖1+ζ‖ ≥ |∑_ζ 1/(1+ζ)|`, the Coulomb sum is therefore squeezed between an explicit
arithmetic ratio below and the cancellation above — the first two-way bridge in the
programme between the zero set and computable Möbius data.

- 2026-08-06 — proved and formalized.

## 2026-08-06 CYCLE 19 FORMALIZED: `RHTower/GibbsLogDerivative.lean`

Wired; build 8660 jobs; no `sorry`; axioms only `propext, Classical.choice, Quot.sound`;
zero warnings.  `RHTower.GibbsGas`: **`eval_derivative_multiset_prod`** (the logarithmic
derivative of a product of linear factors is the Coulomb sum — clean multiset induction,
`field_simp` closes the step), `gibbsPoly_eq_prod_roots`, **`gibbs_coulomb_sum_eq`**
(division-free form), **`gibbsPoly_derivative_eval`** (derivative in the configuration
basis).

Lean notes: `Polynomial.derivative_sum` (not `derivative_finsetSum`) for `Finset.sum`;
`rw … at *` is dangerous when a hypothesis mentions the rewritten head (`hJ` got rewritten
and broke the goal shape) — use an explicit `calc` instead.
