# The integrality anchor law: zero location is an integer squeezed between analysis and discreteness

- **ID:** ULF-INT-001
- **Stage:** 5-failed for the amplification-only search.  Correction: a fixed direct subunit
  squeeze was omitted and remains open as `ULF-DSA-001`; the law survives as a constraint.
- **Type:** CONJECTURE (universal law, frozen) + one design constraint for producers
- **Source:** the four 2026-09-02 retirements (`ULF-PIO-001`, `ULF-SLC-001`, `ULF-IND-001`,
  `ULF-ANC-001`), read against `stuck-route-obstruction-matrix.md` W1–W11, the frontier map's
  six gates, STATUS F379–F382 / CANNOT-182–185 / MUST-119–121, `LeeYangForcingThreshold.lean`,
  the corpus's Kaczorowski–Perelli and Lee–Yang tree modules, and `functional-equation-is-blind-to-rh.md`.
- **Statement:** Every theorem that locates zeros on a line contains exactly one *integrality
  anchor*: a discrete-valued quantity (an integer, a norm of an algebraic integer, a lattice
  count, a signature, a degree) squeezed between an archimedean upper bound and its discreteness
  gap `≥ 1`. Every other step of such a theorem is class-general and blind. Over `ℚ` the zero
  count is the integer, the archimedean slack per integer is the crowd `log t`, and no method in
  the corpus or the literature has an anchor with slack `< 1`. RH is the statement that such an
  anchor exists; every capped method is a real-valued inequality attempting an integer's job.
- **Status:** [ROUTE CLOSED 2026-09-02] [LAW SURVIVES AS CONSTRAINT] [NOT RH] [LEAN: knapsack Euler characteristic, odd-window Mertens identity, window prime, affine invariance]
  table below, each row already certified elsewhere]

## 1. What the four failures say, exactly

| retired route | quantity it bounded | discrete target | slack per integer |
|---|---|---|---|
| pole-plane index (`ULF-PIO-001`) | an integer index, but pair-even | number of off-line pairs | blind: index does not change |
| automorphic created positivity (`ULF-SLC-001`) | `Σ_j h(t_j) ≥ 0`, real | scattering poles | `c/log γ` width: `≍ log γ` zeros per unit |
| two-completion comparison (`ULF-IND-001`) | Littlewood mean, real | `N(σ,T)` | `o(T)`: `T^{1−c}` zeros unresolved |
| inner band (`ULF-ANC-001`) | Laguerre expression, real | pairs with `δ < c/log γ` | needs on-line density `≥ 2/δ²`, an analytic quantity |

In each case the *target* was an integer (a count of zeros) and the *tool* was a real inequality
whose error is at least the crowd. An integer bounded above by `1/2` is `0`; an integer bounded
above by `log t` is unconstrained. That is the whole content of Ceilings C1–C4, of W5 (count
direction), and of the Levinson proportion `1 − c/θ`: the mollifier reduces the slack from
`log T` to `(1 − κ) log T` zeros per unit window but never below one zero.

## 2. The anchor in every proof that works

| theorem | integrality anchor | archimedean side | squeeze |
|---|---|---|---|
| Hadamard–de la Vallée Poussin | residue of the pole `= 1` (an integer multiplicity) | `ζ'/ζ = O(log t)` | width `c/log t`: slack `log t` |
| Weil, curves over `𝔽_q` | intersection numbers `∈ ℤ` on `C × C`; Hodge index signature `(1, ρ−1)` | Castelnuovo `D·D ≤ 2 d₁ d₂` | exact: `|Σ α_i^n| ≤ 2g q^{n/2}` |
| Deligne, Weil I | `α` algebraic integers, weights `∈ ℤ` (cohomological degree), Poincaré duality | Rankin trick on `F^{⊗2k}`, exponent `/k → 0` | exact purity |
| Lee–Yang | polynomial degree finite; Asano contraction exact | none needed | exact circle theorem |
| Kaczorowski–Perelli, degree `< 2` | the degree and conductor are discrete invariants | growth of the standard twist | no Selberg-class element of degree in `(0,1)`; degree `1` classified |
| corpus `prime-ising-tree-cavity-lee-yang` | finite prime-labelled tree, exact cavity recursion | none | real zeros exactly |
| Lagarias–Suzuki / Rankin–Swinnerton-Dyer | two-term dominance (crowd `2`) | `T^{2σ−1}` vs `|φ|` | exact, but zeros are not `Λ`'s (Lean B3) |
| Levinson–Conrey | `N₀` and `N` integers | mollified log-moment | proportion `1 − c/θ`: slack `(1−κ) log T` per window |

Reading: the successful rows are those where the squeeze is *exact* — an integer sits between a
bound and `1`, or a signature is fixed — and the discrete data is intrinsic to a *discrete class*
(varieties over `𝔽_q`, polynomials of fixed degree, finite trees). The capped rows are those
where the discrete side is a zero count and the archimedean side carries the crowd.

## 3. The law and what it explains

> **Integrality anchor law (frozen).** A statement locating zeros is provable exactly when it can
> be written as `0 ≤ I ≤ s` with `I` a discrete-valued invariant of the object and `s < 1` an
> archimedean bound; the reach of every method is the largest region on which its slack `s` is
> `< 1`. Methods valid on a continuous class containing the object (FE-symmetric positive
> functions, Laguerre–Pólya neighbourhoods, kernel classes, general Dirichlet polynomials) have
> slack `≥` the crowd on that class, because the class contains members with any prescribed
> off-line configuration at that resolution.

It explains: **receiver abundance** (F01) — every RH-equivalent statement is `I = 0` for some
integer `I` written as a real inequality; **the crowd** (F379) — slack per integer equals the
zero density; **pair parity** — an even functional cannot separate `I` from `I − 2`; **the
countermodels** — Davenport–Heilbronn, Epstein `h > 1` and Beurling systems are exactly the
members of the continuous classes where no discrete local structure (integer primes, finite
local degree, algebraic coefficients) survives; **"barely true"** (Rodgers–Tao `Λ ≥ 0`) — the
arithmetic object sits on the boundary of the continuous class where the discrete anchor is
lost, so any method that uses only the class sees it as marginal (the corpus's
`closed_forcing_data_not_decide_marginal`); **function fields** — the anchor is intrinsic and
the crowd is a Betti number; **Kaczorowski–Perelli** — rigidity theorems about the Selberg
class are provable precisely because degree and conductor are discrete; **Lee–Yang on prime
trees** (corpus, Lean) — exact because the object is finite.

**Ontological reversal.** RH is not an inequality about `ζ`; it is the assertion that an integer
attached to `ζ` vanishes, and the only way an integer is shown to vanish is by bounding it below
`1`. Analysis over `ℚ` has never produced such a bound for the right-half count. A producer may
either give one fixed source bound below one or manufacture a family whose slack tends to zero.
Amplification is sufficient, not necessary.

## 4. Risky consequences

- **P1 (slack quantization).** For every method in the corpus, the ratio (analytic slack) /
  (integrality gap) at height `t` is `≥ c · d · log t` for degree-`d` objects, with equality
  exactly for de la Vallée Poussin-type arguments; mollifiers reduce the constant, never the
  order. Falsifier: any argument with slack `o(log t)` per zero at all heights.
- **P2 (integer receivers are absent).** No RH-equivalent statement in the corpus is of the
  form "an explicitly defined *integer-valued* arithmetic function of `x` is identically zero"
  whose non-vanishing has an unconditional lower bound `1` *and* an unconditional upper bound
  tending to `0` under amplification. Prediction: a corpus census finds none; every receiver is
  real-valued or a count with only lower bounds. Falsifier: an integer receiver with an
  amplifiable squeeze already present.
- **P3 (countermodel classification).** A class of FE-symmetric objects admits off-line zeros
  iff it has no discrete local invariant (integer primes, finite local degree, discrete
  conductor). Checked: DH (superposition, no Euler product), Epstein `h>1` (superposition),
  Beurling (non-integer primes); conversely no counterexample is known in any class with all
  three. Falsifier: an FE-symmetric Euler-product object with integer primes and finite local
  degrees having an off-line zero.
- **P4 (corrected dichotomy).** A producer must supply either a direct invariant `I` with
  `0 <= I <= s < 1`, or an amplifiable family `I_k` with `I_k >= 1` off line and
  `I_k <= f(k) -> 0`. Ferrero--Washington's `mu = 0` is evidence for the direct branch: positive
  content forces all-depth congruences and equidistribution contradicts them.

## 5. The design constraint (not a route)

Any future producer card must state, before any inequality is written: (i) the discrete
invariant `I`; (ii) why `I >= 1` follows from one off-line quartet; and either (iii-a) one direct
source bound `I <= s < 1`, or (iii-b) an amplification `I_k <= s(k) -> 0`. Cards that supply
neither are real-valued inequalities capped by §3. This corrects MUST-122.

Candidates for `I` that fail (i)–(iv) and are hereby closed: zero counts in fixed windows
(slack `log t`); Pontryagin/pole-plane indices (pair-even, blind); Littlewood/Jensen counts
(slack `O(log T)` horizontal term); sign-change counts of `Z` in short intervals (no pointwise
lower bound at crowd scale); Möbius exact sums `Σ_{d∣n} μ(d)` (exactly `0/1` but divisor-closed,
not interval-closed: the knapsack truncation to `n ≤ x` is `M(x)` and the exactness is lost
precisely there — the squarefree complex `Γ_x = {S ⊆ primes : ∏S ≤ x}` is a shifted complex with
reduced Euler characteristic `−M(x)` and homology a wedge of spheres indexed by odd squarefree
`n ∈ (x/2, x]`, so its Betti numbers are large and only their alternating sum cancels).

## Gates
- [ ] 0 → 1: corpus census for P2 recorded; one candidate `I` with (i)–(iv) proposed or the
  census closes the card as a pure constraint.
- [ ] 1 → 2 / 2 → 3 / 3 → 4.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** —
- **Strongest positive survivor:** —
- **New insight:** —
- **Status:** —

## Log
- 2026-09-02 — created in 0-backlog from the four-retirement synthesis; frozen before proof
  search; no computation used; the squarefree-complex remark is elementary (crosscut theorem,
  shifted complexes) and recorded only to close that candidate.

## Paper conjecturing loop on the discrete invariant `I` (2026-09-02)

Each candidate is tested against (i) discreteness, (ii) `I ≥ 1` from one quartet,
(iii) an unconditional bound `s(k)`, (iv) `s(k) → 0`.

| candidate `I` | (i) | (ii) | (iii)/(iv) | killed by |
|---|---|---|---|---|
| zero count in a window or half-plane | ✓ | ✓ | slack `≥ log t` per integer | ceilings C1–C4, Selberg ledger, zero-density `T^{1−c}` |
| pair-even indices (pole plane, Pontryagin) | ✓ | ✗ | — | `pairLedger_even`: even in `δ` |
| Fredholm/Toeplitz index of `ζ` along vertical lines | ✓ | ✓ | index = winding = argument principle; `T_{φ^k}` multiplies index and slack alike | crowd |
| affine rescalings `∏ ζ(a_i s + b_i)^{e_i}` (the `ζ`-algebra) | — | — | relative displacement `(Re ρ − ½)` is an affine invariant; convolution powers keep the abscissa | `relativeDisplacement_affine` (Lean) |
| Deligne tensor amplification | ✓ | ✓ | needs global zeros to be *local* eigenvalues at a point (`Spec 𝔽₁`) | absent; this is the corpus's F₁ open core |
| Euler characteristic of the squarefree knapsack complex `Γ_x` | ✓ | ✗ | `χ̃(Γ_x) = −M(x)` (Lean); `M(x) = ∑_{odd n ∈ (x/2,x]} μ(n)` (Lean) is the alternating Betti sum of a shifted complex whose Betti numbers count odd squarefree `n ∈ (x/2, x]` by `ω(n)`; the top window always contains an odd prime (Lean) | no cancellation in Betti numbers; only parity of `ω` cancels |
| Iwasawa `μ`, `λ` (Ferrero–Washington `μ = 0` is an instance of the law) | ✓ | — | squeezed by digit equidistribution | concerns `p`-adic zeros; no bridge to complex zeros |
| Kloosterman/Petersson integrality (Weil bound) | ✓ | — | exact per modulus | zeros enter only on `Re s = 1` (`ULF-SLC-001` P1) |
| Hecke's CM-average `∑_{Cl(D)} E(z_a, ρ) = 0` | — | ✓ | exact for every `D` | no discrete-valued quantity |

**Corrected verdict.** No audited amplification candidate satisfies the gate.  The conclusion that
only an F1 local-eigenvalue realization remains was too strong: the audit omitted a direct fixed
subunit source invariant.  `completedSEMContourIndexZ` proves source-defined integer winding is
available, while its existing use is zero-centred.  `ULF-DSA-001` keeps open the distinct problem of
globalizing that winding and bounding its relative completed index below one without amplification.

## No-go closure
- **Exact killing theorem/mechanism:** the table above; Lean certificates
  `RHTower.relativeDisplacement_affine` (no affine amplification),
  `RHTower.sum_primeSets_neg_one_pow` and `RHTower.sum_moebius_eq_sum_odd_window` (the knapsack
  complex's Euler characteristic is the top-window odd Möbius sum, so its Betti numbers carry no
  cancellation), `RHTower.exists_odd_prime_window` (the Betti numbers do not vanish),
  `pairLedger_even` (indices are pair-even); module `RHTower.MertensOddWindowKnapsack`.
- **Strongest positive survivor:** the identities above, unconditional; the law's audit table
  (§2) as a classification of every zero-location proof by its anchor; MUST-122.
- **New insight (corrected):** the amplification search and the F1 search describe one branch, not
  every possible branch. A discontinuous source content/winding with one direct subunit bound is
  not excluded by `NoDiscreteInvariant` and was not audited here.
- **Status:** internal audit; module `lake build` green, axioms `propext, Classical.choice,
  Quot.sound`, wired into `GaloisForLFunctions.RHTower`.

## Log (continued)
- 2026-09-02 — conjecturing loop run on paper (nine candidates); route closed; identities
  formalized; card moved to 5-failed.
- 2026-09-02 — correction after Ferrero--Washington audit: amplification is not mandatory;
  direct relative source winding moved to `ULF-DSA-001`; exclusivity verdict withdrawn.
