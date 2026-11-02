# Cohomology of Windows of Spec ℤ (CWS)

Namespace `GaloisForLFunctions.CohomologyOfWindowsOfSpecZ`; umbrella `CohomologyOfWindowsOfSpecZ.lean`.
Every theorem is unconditional. Theorems named `riemannHypothesis_iff_*` are proved equivalences,
not proofs of RH.

## 1. Motivation

The corpus has built every layer of an arithmetic Hodge theory of the scaling surface except the one
that produces positivity. The degeneration of the complete Weil family (ADT, AHD) is a complete
dictionary: its first-order structure is a point count, `J(m) = J(1)·#ℙ⁷(ℤ/m)`; its second-order
structure on a horizon window is Weil's form `Q(H)` of the synthesized window test plus a prime-free
positive term. RH is the sign of that one form on windows of every length
(`riemannHypothesis_iff_halfWeight_nonneg`). A theory of degenerations says where the sign lives; it
does not supply it.

Over `𝔽_q` the sign is never an estimate. Weil reads it from intersection numbers that are counts,
Stepanov from auxiliary sections whose vanishing is counted, Deligne from tensor powers with Euler
products. In each proof a cohomology group is finite, `h¹ ≥ 0` because it is a dimension, and an
identity (Riemann–Roch, Lefschetz) converts that free inequality into the bound.

CWS is the theory that attaches to each **window** of `Spec ℤ` — a scale cutoff `e^A`, equivalently
the interval `[−A, 0]` of the scaling line together with the prime powers `n ≤ e^A` that act on it —
a finite arithmetic object whose `h¹` is Weil's window form, and asks what it must be for `h¹` to be
nonnegative for a structural reason. Its work is:

1. to determine the **window datum** exactly: which primes act, how the creation potential is paid,
   what the canonical class is, how the prime jumps fold the window, what the window's Serre duality
   and Frobenius at infinity are;
2. to decide which **carriers** can realize the window `h¹` (a count, a capacity, a placement), and to
   prove which cannot;
3. to **calibrate**: curves over `𝔽_q` (where the window object exists and its `h¹` is a count), the
   prime-free windows `A < log 2`, the first prime `log 2 ≤ A < log 3`;
4. to locate **selection**: which axiom of a window theory fails for the fakes.

## 2. Objects

| Object | Meaning |
|---|---|
| Window `W_A` | the interval `[−A, 0]` of the scaling line, `A ≥ 0`; multiplicatively the scales `[e^{−A}, 1]` |
| Window test | real `C²` function `H` supported in `W_A`; `H = e^{y/2}h` synthesizes a horizon block |
| Window form | `Q_A(H) = Q(H)`, Weil's quadratic form of `ζ` on window tests |
| Active prime powers | `P_A = {n ≤ e^A : Λ(n) ≠ 0}`, jump weights `w_n = Λ(n)/√n`, jump lengths `ℓ_n = log n` |
| Window Markov form | `M_A(H) = V_A‖H‖² + J_∞(H) + Σ_{n∈P_A} w_n‖H − H(·+ℓ_n)‖²`; `J_∞` the archimedean Lévy jump energy |
| Creation potential, canonical degree | `V_A = Ω(0) − 2Σ_{n≤e^A} w_n`; `deg K_A = −V_A` |
| Pole plane | `c(H) = ⟨2cosh(u/2), H⟩`, `s(H) = ⟨2sinh(u/2), H⟩`; pole term `½c² − ½s²` |
| Canonical density | `k_A(u) = Σ_{n∈P_A} w_n (1[u ≤ −ℓ_n] + 1[u ≥ ℓ_n − A])` on `W_A`: in-window Hecke neighbours |
| Fold of `T_n` | the translation `I_n^- = [−A, −ℓ_n] → I_n^+ = [ℓ_n − A, 0]`; fold energy `∫_{I_n^-}(H(u) − H(u+ℓ_n))²` |
| Window involution | `σ_A H(u) = H(−A − u)`; on transforms `Ĥ(s) ↦ e^{−(s−½)A} Ĥ(1−s)` |
| Window index | `ι(A)`: negative squares of `Q_A` on window tests |
| Window genus | `g(A, ε)`: largest dimension of a subspace of window tests with `|Q_A| ≤ ε‖·‖²` (near radical) |
| Window realization | a real inner product space `E_A` and a linear map `r_A` with `Q_A(H) = ‖r_A H‖²` |
| Window correspondences | integral combinations of scalings by `log r`, `r` in the window; Rosati `ξ ↦ ξ'`; window naive heights |
| Curve window | for a curve over `𝔽_q`: the Frobenius-cyclic subspace of `H¹` generated in degrees `0, …, n` |

## 3. Language

- **Window of length `A`**; **active** prime power: `n ≤ e^A`; **departing** jump: one that leaves the
  window (`ℓ_n > A`, or the part of an active jump that exits).
- **Stage** of a window: prime-free (`A < log 2`), first-prime (`log 2 ≤ A < log 3`), and so on; a new
  Euler factor enters at each `A = log p`.
- **Window `h¹`**: half the window form, `h¹_A(H) = ½Q_A(H)`; it is the primitive `h¹` of LST's Künneth
  Riemann–Roch restricted to window tests.
- **Carrier** of the window `h¹`: an object that makes it nonnegative for a structural reason — a
  **count** (a dimension, a cardinality, a log-count), a **capacity** (a Poincaré inequality for the
  window Markov form), a **placement** (an operator whose spectrum lies on the critical line).
- **Soft** property: holds for every jump weight, every Gamma factor, or every datum of a family;
  **selective**: fails on a fake (golden curve, prime flips, Epstein lattices, positive degree-two FE data).
- **Local** in the window: depends only on the Euler factors at `p ≤ e^A`.

## 4. Mechanisms

**A. The window datum.**
1. *Locality.* On a window of length `A` only the prime powers `n ≤ e^A` act by a jump; a jump that
   leaves the window pays exactly its own creation `2w_n‖H‖²`. The window form is the Markov form at
   level `⌊e^A⌋` plus the pole plane, and does not depend on any Euler factor at `p > e^A`.
2. *The canonical class.* The creation of an active prime splits pointwise into the part paid by
   exits (the jump leaves the window on one side) and an in-window remainder. The remainder is the
   canonical density `k_A`: Weil's window form is
   `Q_A(H) = Ω(0)‖H‖² + J_∞(H) + Σ_{n∈P_A} w_n (fold energy of T_n) − ∫ k_A H² + pole`.
   Its total mass, the degree of the window's canonical class, is the Riesz mean
   `deg k_A = 2Σ_{n≤e^A} w_n (A − log n) = 2∫_0^A ψ_{1/2}(e^t) dt`, symmetric under the window
   involution; its main term is the pole term of the window indicator.
3. *Folds.* Each active `T_n` identifies the two ends `I_n^±` of the window by a translation; its jump
   energy lives on the fold and its creation on the two ends. On the first-prime stage there is exactly
   one fold, the graph of `T₂`.
4. *Serre duality and Frobenius at infinity.* The window involution `σ_A` is an isometry of `Q_A`; on
   transforms it pairs `s` with `1 − s` with multiplier `e^{−(s−½)A}`, of modulus one exactly on
   `Re s = ½`.
5. *Gluing at the pole.* The pole plane adds one positive and one negative square; the window index
   and the index of the Markov form differ by at most one.

**B. Carriers.**
6. *Count (Mechanism A).* A naive height on window correspondences — a count at bounded distance from
   the integral Rosati form — forces Rosati positivity on the window by Tate's limit law; Rosati
   positivity at every window is the orbit Hodge index, which is RH.
7. *Capacity (Mechanism B).* `Q_A ≥ 0` on pole-orthogonal window tests is the Poincaré inequality
   `jump energy ≥ deg K_A ‖H‖²` for the window Markov form; with the canonical density it is a
   Schrödinger inequality on the interval with a jump Laplacian.
8. *Placement (Mechanism C).* A definite structure on the scattering channel of `Λ(s)/Λ(s+1)` places
   its poles; the window involution is the window shadow of Frobenius at infinity.

**C. Calibrations.**
9. *Curves.* Over a curve the window form of length `n` is the Gram form of the Frobenius orbit of one
   vector in `H¹`; the window genus is the rank of that orbit and saturates at the number of distinct
   Frobenius eigenvalues (`≤ 2g`); in genus one the window `h¹` of `a + bF` is `deg(a + bF) = #ker`.
10. *Prime-free windows.* The window `h¹` is the Lévy jump count of the Gamma factor plus a constant and
    the pole; for short windows the count alone pays it.
11. *The first prime.* One fold, the graph of `T₂`, of length `A − log 2`, sitting where the
    archimedean exit charge is largest.

## 5. Questions the programme answers

| Question | Shape of the answer |
|---|---|
| What object has Weil's window form as its `h¹`? | The window datum with the Künneth count: `h¹ = Künneth part + ½Q_A`. A Hilbert realization exists iff RH (under RH the zero map is one); none is finite-dimensional on any window of positive length. Over `𝔽_q` the window object is the Frobenius-cyclic subspace of `H¹`, its `h¹` a count. |
| What set does `τ_x(ξ⋆ξ′)` count, up to bounded error? | Windowed Tate law: a count at bounded distance on window correspondences exists iff window Rosati positivity; on prime-free windows the count is the Lévy jump count. |
| Is `β` the dimension of an ambient `ℙ^β`; is there a scheme whose point counts give the second order? | First order: `J_{β+1}(m)/φ(m) = #ℙ^β(ℤ/m)` for every `β`. Second order: the prime-free term is `β` times the count; the zero-carrying term is Weil's window form, which no local count determines. |
| What pays the creation potential; what is the degree of the window's canonical class? | Exits pay the departing and exiting creation exactly; the rest is the canonical density `k_A` of degree `2∫_0^A ψ_{1/2}(e^t)dt`, which the fold energies, the archimedean jumps and the pole must pay. |
| What are Stepanov's auxiliary sections on a window? | Over `𝔽_q`: Stepanov's count pays the window `h¹` (hyperelliptic curves of every genus). Over `ℤ`: the tests vanishing on the finite low-frequency divisor and at the pole; on them `h¹` is coercive, and the window index is bounded by the degree of that divisor. |
| What lattice carries the sections of a window (rank `≈ 2e^{2a}`), with what metric? | The rank is the Young conjugate of the archimedean zero density, attained at the Landau height `2πe^{2a}`: the nonzero integers of size `≤ e^{2a}`, the Gaussian lattice count `exp h⁰_ℤ(2a)` of `Spec ℤ`; the Gamma factor enters as that Gaussian and as the Lévy jump measure. |
| Why `ζ` and not an Epstein function or a positive degree-two series? | Windows below `log p` cannot see the Euler factor at `p`, so no window of bounded length selects; Epstein and positive degree-two data fail the Euler axiom; the golden curve satisfies every count axiom and fails only the window `h¹`. |

## 6. Tools

**Developed in CWS.** Window tests and the window datum; the canonical measure of a window (exit/remainder
splitting, Riesz degree, symmetry); folds of prime jumps and the first-prime decomposition; the window
involution and its transform multiplier; index and genus functions of windows; window realizations and the
zero map; windowed naive heights; curve windows; the selection battery of window axioms; Young duality for
the window genus.

**Used from the corpus.** Weil's form, its Lévy and Markov forms (SSHA, RHTower `WeilMarkovPoleCapacity`);
the window criterion and the primes of a window (AHD); Künneth Riemann–Roch, the jump count of prime-free
cycles, the finite divisor, Stepanov over `𝔽_q` (LST); scaling surface, curve data, golden datum, Hodge
defect filtration, Landau–Widom near radical and genus function (ACS); Tate's limit law (AET); the
correspondence algebra (AOG); the Jordan count law (AHD).

**To develop.** Dirichlet forms and Poincaré inequalities for arithmetic jump kernels on intervals;
Arakelov `h⁰` on lattices of growing rank; indefinite theta functions of the Hecke lattice; Krein and
Lax–Phillips structures for the scattering channel; measure rigidity of resonant states.

## 7. Open research topics

1. **A count at the first prime.** An identity `Q_A = (Lévy jump count) + (a count attached to the fold
   of T₂) + (squares)` on `log 2 ≤ A < log 3`, or the exact obstruction.
2. **The whole prime-free window as a count.** A Poincaré inequality for the Lévy form on an interval
   of length `< log 2` with the sign structure of the pole.
3. **The window capacity.** Poincaré inequalities `fold energies + J_∞ ≥ ∫ k_A H² − pole` uniform in
   `A` (RH).
4. **Window naive heights.** A count on window correspondences at bounded distance from the integral
   Rosati form (RH at every window).
5. **The second order as a count.** Whether the zero-carrying part of the second-order term is the
   `h¹` of a scheme-like object over `ℤ`.
6. **Window Frobenius at infinity.** An operator on the window object whose fixed line is `Re s = ½`
   and which places the poles of `Λ(s)/Λ(s+1)`.

## 8. Pillar theorems

| Theorem | Module |
|---|---|
| Window datum: locality, level independence, translation and reflection invariance; RH ⇔ every window | `TheWindowDatum` |
| Canonical measure: exit/remainder splitting, the window form as fold energies minus canonical density, Riesz degree, symmetry | `TheCanonicalClassOfAWindow` |
| First-prime fold: one fold on `[log 2, log 3)`, the graph of `T₂` | `TheFirstPrimeFold` |
| Window involution: isometry, transform multiplier, unitary locus `Re s = ½` | `TheFrobeniusAtInfinityOfAWindow` |
| Window index and genus: monotone, finite, zero on short windows, limit = Hodge defect; Young conjugate | `TheWindowIndex`, `TheWindowGenusIsAYoungConjugate` |
| Realizations: exist iff RH, never finite-dimensional | `WindowRealizations` |
| Windowed Tate law | `WindowNaiveHeights` |
| Curve windows: Gram realization, genus = rank of the Frobenius orbit, count in genus one | `TheWindowCohomologyOfACurve` |
| Selection: windows below `log p` are blind to `p`; the fakes against the axioms | `TheSelectionBatteryOfWindows` |

## 9. Traps

| Trap | Truth |
|---|---|
| A window is a semilocal object `{∞} ∪ {p ≤ e^A}` | No semilocal or trace carrier is positive; the window is global, with finitely many active jumps |
| The creation potential is a cost of all primes | Departing primes pay their own creation exactly; only the in-window canonical density remains |
| Locality selects `ζ` | Locality holds for every weight; windows below `log p` cannot see the Euler factor at `p` |
| A finite-dimensional window cohomology | `Q_A` has infinite positive index on every window of positive length |
| Positive jump weights (Markov) give the sign | Markov holds for every nonnegative weight, including fakes; the pole is the only anti-Markovian term |
| The pole term is a nuisance | It is the main term of the canonical degree and one negative square |
| Positivity of window indicators is soft | It is a one-sided Riesz-mean prime number theorem with square-root error |
| The window involution is a symmetry that orients | It is an isometry on every datum; only its multiplier distinguishes the line |

## 10. Place in the research and relation to other programmes

| Programme | Relation |
|---|---|
| `ArithmeticHodgeTheoryOfDegenerations`, `ArithmeticDegenerationTheory` | the degeneration whose second order is the window form; window criterion, primes of a window, Jordan count law |
| `LatticeSectionTheory` | Künneth Riemann–Roch, primitive `h¹ = ½δ`, jump count of prime-free cycles, finite divisor, Stepanov over `𝔽_q`; CWS restricts these to windows |
| `ArithmeticCastelnuovoSeveri` | scaling surface, curve data and golden datum, Hodge defect filtration, near radical and genus function |
| `ArithmeticOrientationGeometry`, `ArithmeticEffectivityTheory` | correspondence algebra, Rosati involution, Tate's limit law, theta `h⁰` of `Spec ℤ` |
| RHTower `WeilMarkovPoleCapacity` | Markov form, sinh capacity, Markov property |
| `CriticalArithmeticCorrelationTheory`, `RenormalizedIntersectionTheory` | the complete family and its pole hyperplane, whose horizon layer is the window form |
| WD, PM routes | window integers reduce to precision (WD); placement is the PM question for `Λ(s)/Λ(s+1)` |

## 11. Success criteria and criteria for contributions

The programme succeeds when the window `h¹` is realized as a count, a capacity or a placement at every
window length — first at the whole prime-free window, then one prime at a time — or when it is proved
which of these carriers cannot exist. Every question of §5 must have a theorem as its answer.

A contribution must:
1. be stated on window tests of a fixed length, or as a law in the length;
2. say which part of the window form it controls: archimedean jumps, fold energies, canonical density,
   pole;
3. say what it does on the fakes (golden curve, prime flips, Epstein lattices), since a law that holds
   on them is soft;
4. be an identity or a structural inequality, not an estimate that loses a factor growing with `A`;
5. be unconditional; implications into RH and equivalences are labelled as such.

## 12. Big picture

Weil's form on a window of length `A` is a finite arithmetic object: an archimedean jump energy, finitely
many folds of the window by the active prime powers, a canonical density that the creation potential
leaves on the window after the exits have paid their share, and a pole plane with one negative square.
Every structural identity of this object holds for every weight and Gamma factor; the sign does not.
Over `𝔽_q` the same object is the Frobenius orbit of a vector in a `2g`-dimensional `H¹`, and its `h¹`
is a count. The field's task is that count over `ℤ`: an `h¹` on the window datum that is nonnegative
because it counts, and an identity that turns it into Weil's window form.
