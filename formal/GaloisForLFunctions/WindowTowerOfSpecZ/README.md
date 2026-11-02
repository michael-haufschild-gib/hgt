# The Window Tower of Spec ℤ (WTZ)

Namespace `GaloisForLFunctions.WindowTowerOfSpecZ`; umbrella `WindowTowerOfSpecZ.lean`.
Every theorem is unconditional. Theorems named `riemannHypothesis_iff_*` are proved equivalences,
not proofs of RH.

## 1. Motivation

Weil's criterion has become a statement about **windows**: RH holds iff Weil's form `Q` is
nonnegative on every test supported in `[−A, 0]`, for every length `A`. One window is a finite
problem: it reads only the prime powers `n ≤ e^A`, its negative index is finite and Shannon-bounded,
and its form is archimedean jumps, one fold per active prime power, a canonical class and a pole
plane (CWS). RH is not a property of one window. It is **uniformity in `A`**: a law that holds along
the whole tower `A ↦ W_A` as the length grows and the prime powers enter one at a time.

Three proved laws fix the shape of what is missing (CWS, ACS, LST): the window `h¹` has no
finite-dimensional or finite-rank realization; its effective rank grows like `2e^A`; counts already
pay everything except the primitive part `½Q`. Over `𝔽_q` the same situation is resolved by a tower
of growing rank with control theorems — Iwasawa theory, base change in the `𝔽_{q^m}` tower — not by
the cohomology of one variety. WTZ is the theory of the window tower of `Spec ℤ` as such: its
algebra, its transition maps and their control, its growth law in `A`, its Tate pieces, its
lattice, and the place where its positivity must come from.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Window module | `windowSupported A` | real functions vanishing off `[−A, 0]`; `F_A ⊆ F_B` for `A ≤ B` |
| Window shift | `windowShift t` | `(T_t H)(u) = 1_{u≤0} H(u − t)`: the fold by `t` moved toward the right end |
| Window representation | `windowRep A` | `ρ_A(f)H = Σ_{n≤e^A} f(n) n^{−1/2} T_{log n} H`, a ring map from arithmetic functions |
| Window algebra | `truncIdeal N`, `D_N` | arithmetic functions modulo those vanishing on `[1, N]`; `D_{⌊e^A⌋} ≅ image of ρ_A` |
| Window zeta and von Mangoldt operators | `ρ_A(ζ)`, `ρ_A(μ)`, `ρ_A(Λ)` | the sum of all Hecke shifts, its inverse, its logarithmic derivative |
| Position operator, Tate twist | `positionOp`, `ρ_A(f·n^k)` | `(MH)(u) = uH(u)`; twisting by `n^k` is conjugation by `e^{ku}` |
| Jordan family | ADT `jordanTotient` | `J_k(m) = Σ_{d∣m} μ(m/d) d^k`; `J_{β+1}(m) = φ(m)#ℙ^β(ℤ/m)` (AHD) |
| Window negativity | `windowNegativity A` | least `λ ≥ 0` with `Q ≥ −λ‖H‖²` on window tests of length `A` |
| End profile | `endProfile` | `φ(t) = W(t) − ψ_{1/2}(e^t)`: archimedean exit tail minus prime count at distance `t` from an end |
| Window potential | `windowPotential A` | `V_A(u) = Ω(0) + φ(−u) + φ(A + u)` |
| Atomic lattice | atoms `φ(· + log m)`, `m ≤ e^A` | the regular representation of `D_{⌊e^A⌋}` inside the window |

From CWS: `IsWindowTest`, `windowLevel = ⌊e^A⌋`, `foldEnergy`, `foldSym`, `canonicalDensity`,
`halfChebyshev`, `canonicalDegree`, `windowIndex`, `windowGenus`.

## 3. Language

- **Tower**: the family `A ↦ (F_A, ρ_A, Q|_{W_A})`; **level** `N = ⌊e^A⌋`; **stage** `n`: `log n ≤ A < log(n+1)`.
- **Transition**: `D_{N+1} → D_N` (truncation) on the algebra side, `F_A ⊆ F_B` on the module side.
- **Small extension**: a surjection of local algebras whose kernel is killed by the maximal ideal.
- **New fold** at stage `n`: the shift `T_{log n}`; it enters as a socle element.
- **Cotangent space** of the window algebra: `m/(m² + I_N)`; its basis is the primes `≤ N`.
- **Tate piece**: a value of the Jordan family at a positive integer `k` — a point count of
  `𝔸^k∖0` (primitive vectors) over a residue ring. **Non-Tate piece**: its derivative at `k = 0`.
- **Window negativity**, **negativity exponent**: `λ(A)` and `limsup log λ(A)/A`.
- **Interior energy**: the jump energy of jumps that stay inside the window (archimedean and prime
  folds). **Exit charge**: what the archimedean jumps that leave the window pay.
- **Soft**: true for every weight on the prime powers (fakes included). **Selective**: fails on a fake.

## 4. Mechanisms

**A. The window algebra.** The fold of a window by `t ≥ 0` is the compressed translation
`T_t`; compressions of translations by nonnegative amounts to an interval compose exactly
(`T_s T_t = T_{s+t}`) and vanish past the length (`T_t = 0` for `t > A`). Hence `ρ_A` turns
Dirichlet convolution into composition: the arithmetic of a window is a representation of the ring
of arithmetic functions, faithful exactly modulo the functions vanishing on `[1, ⌊e^A⌋]`. Weil's
window form is

`Q(H) = Ω(0)‖H‖² + J_∞(H) − 2⟨ρ_A(Λ)H, H⟩ + 2Ĥ(0)Ĥ(1)`,

and `ρ_A(Λ)` is the logarithmic derivative of the window zeta operator along the position:
`ρ_A(Λ)ρ_A(ζ) = ρ_A(log) = [M, ρ_A(ζ)]`. The truncated Euler product is exact in the window algebra.

**B. The tower and its control.** The modules nest equivariantly (`ρ_B = ρ_A` on `F_A`); the
algebras form an inverse system of local Artinian rings with limit the full Dirichlet ring. Each
transition `D_{N+1} → D_N` is a small extension with one-dimensional kernel spanned by the new fold;
the new fold composes to zero with every other fold until stage `2(N+1)`; the maximal ideal of `D_N`
is nilpotent of order `⌊log₂ N⌋ + 1`; the cotangent space has the primes `≤ N` as a basis. The
primes are exactly the generators that a window can see; the prime powers and composites are
products in the tower.

**C. Tate pieces and the non-Tate piece.** The Jordan family `k ↦ ρ_A(J_k)` is the window ratio
`ζ_A(s − k)/ζ_A(s)` (Tate twist by `k` divided by the window zeta operator). At `k = β + 1` its
coefficients are `φ(m)#ℙ^β(ℤ/m)`, the Tate pieces of the degeneration; at `k = 0` it is the identity;
its derivative at `k = 0` is `ρ_A(Λ)`. So

`Q(H) = Ω(0)‖H‖² + J_∞(H) + 2Ĥ(0)Ĥ(1) − 2 (d/dk)|_{k=0} ⟨ρ_A(J_k)H, H⟩`:

the Tate pieces are values of one family and Weil's arithmetic window term is its derivative at
dimension zero.

**D. The growth law.** On a window the pole plane is `½⟨c_A,H⟩² − ½⟨s_A,H⟩²` with `c_A, s_A` the
cosh/sinh centred at the window midpoint, so its exact capacity is `2 sinh(A/2) − A`. With the
canonical class, `Q ≥ −(deg K_A + 2 sinh(A/2) − A)‖H‖²`: the window negativity is `O(A e^{A/2})`,
exponent `≤ ½` (the trivial strip). If some zero has depth `> σ`, the negativity is not `O(e^{σA})`.
Hence an exponent `< ½` is a zero-free strip and subexponential negativity is RH.

**E. The end profile.** Every jump of a window test, archimedean or prime, splits into a fold
inside the window and an exit. Exits of archimedean jumps pay the charge `W(d)` at distance `d` from
an end; prime jumps leave the canonical density `ψ_{1/2}(e^d)`. So

`Q(H) = (interior jump energy) + ∫ V_A H² + pole`, `V_A(u) = Ω(0) + φ(−u) + φ(A + u)`,

with one universal end profile `φ(t) = W(t) − ψ_{1/2}(e^t)`: positive and logarithmically large near
an end, negative like `−2e^{t/2}` in the bulk. Positivity of a window is a Poincaré inequality of the
censored jump process against this potential.

## 5. Questions the programme answers

| Question (obstacles §2.7) | Answer |
|---|---|
| What are the restriction maps `W_A → W_{A'}` and their control theorem? | Equivariant inclusions of window modules over the truncation `D_{⌊e^{A'}⌋} → D_{⌊e^A⌋}`; each step is a small extension whose kernel is the new fold, a socle element; the cotangent space is the primes. |
| What is the count attached to a fold `T_n`? | In the algebra, `T_n` is the basis element `δ_n`; the window zeta operator `Σ T_n` counts factorizations (`ρ(ζ^k) = ρ(d_k)`); the arithmetic part of `Q` is the logarithmic derivative of that count. |
| Is there a scheme over `ℤ` whose `ℤ/m`-points give the twisted counts and whose "conductor-one" part is the window form? | The punctured affine spaces `𝔸^k∖0` (primitive vectors), with `k` as a parameter: their counts `J_k(m) = φ(m)#ℙ^{k−1}(ℤ/m)` are the Tate pieces, and Weil's arithmetic window term is the `k`-derivative at `k = 0`. |
| What lattice of rank `≈ 2e^A` carries the sections; what metric? | Atoms at `log m`, `m ≤ e^A`, carry the regular representation of `D_{⌊e^A⌋}` (rank `⌊e^A⌋`); the window genus is twice that rank to main order; the metric is Weil's Gram on atoms (Gamma factor as Lévy kernel between atoms, Gaussian width of an atom). |
| What growth law does the tower obey? | Negativity exponent in `[zero width, ½]`; `< ½` is a zero-free strip; subexponential is RH. |
| Which axiom fails for the fakes? | Every tower structure (algebra, control, Jordan family, end profile) holds for every weight; flip twins agree with `ζ` on every window below their prime. Only the sign of `Q` along the whole tower selects. |

## 6. Tools

**Developed.** Window shifts and the window representation of the Dirichlet ring; truncation
ideals and small-extension calculus; the degree derivation as a commutator with the position;
Tate twists as conjugation by exponentials; the Jordan family and its derivative at `0`; the
centred pole plane and its exact capacity; window negativity and its growth laws; exit
decomposition of Lévy jumps on an interval.

**Used from the corpus.** CWS (window tests, folds, canonical class, index, genus, Tate law,
selection); AHD/ADT (Jordan totient, `#ℙ^{k−1}(ℤ/m)·φ(m) = J_k(m)`); SRT (two-bump negativity rate);
ACS (scaling surface, zero configurations); RHTower `WeilMarkovPoleCapacity` (Markov form, Lévy
jumps, pole pairings); mathlib `ArithmeticFunction`.

**To develop.** Nonlocal Poincaré inequalities for the censored arithmetic jump process with the
end-profile potential; graph Schur complements on the atomic lattice; Arakelov `h⁰` on lattices of
growing rank; Wiener–Hopf factorization of the window symbol; Krein-space structures for the
reflection `σ_A`.

## 7. Open research topics

1. **Window capacity uniform in `A`.** Interior jump energy `≥ −∫V_A H² − pole` on every window
   (equivalent to RH). The potential is positive near the ends and `≈ −4e^{A/4}` at the centre.
2. **The count for the symmetric fold masses.** A positivity for the logarithmic derivative of the
   window zeta operator; the first instance is the fold of `T₂`.
3. **Critical lengths.** The lengths at which the window index jumps, and the control of index jumps
   across a stage.
4. **The derivative at dimension zero.** Which positivity of the Tate family `k ↦ ⟨ρ_A(J_k)H,H⟩`,
   `k > 0`, survives the derivative at `k = 0`.
5. **The growth exponent.** Close the gap between the zero width and the exponent of window
   negativity without the no-clustering hypothesis.

## 8. Pillar theorems

Filled as the modules are formalized.

## 9. Traps

| Trap | Truth |
|---|---|
| The window algebra is the semilocal Euler factor algebra at `p ≤ e^A` | It is the full truncated Dirichlet ring: composites are products, but truncation is by `n ≤ N`, not by primes |
| The tower is a direct limit of finite objects carrying `h¹` | The algebras are finite-dimensional; the modules are not, and no window has a finite-dimensional realization (CWS) |
| A new prime at stage `p` is a large perturbation of the window | Algebraically it is a socle element; its analytic size is the end mass, not the norm |
| Counting coefficients make the window zeta operator selective | Epstein zeta functions count lattice points with the same algebra; counts are soft |
| The Tate pieces' positivity transfers to Weil's form | Weil's term is a derivative at `k = 0`, not a value |
| The pole plane costs `A e^A` on a window | Its exact capacity is `2 sinh(A/2) − A`, exponent `½` |

## 10. Place in the research and relation to other programmes

| Programme | Relation |
|---|---|
| `CohomologyOfWindowsOfSpecZ` | one window at a time: datum, folds, canonical class, index, genus, Tate law, selection. WTZ is its tower: transitions, control, growth, Tate pieces |
| `ArithmeticHodgeTheoryOfDegenerations`, `ArithmeticDegenerationTheory` | Jordan totient and the projective-space count law; WTZ places the Tate pieces and Weil's form on one family |
| `SquareRootThreshold` | two-bump negativity rate, ground-energy rate vs zero width; WTZ reads them as the growth law of the tower |
| `LatticeSectionTheory` | Künneth Riemann–Roch, exterior jumps of prime-free cycles; the end profile is the full exterior charge |
| `ArithmeticCastelnuovoSeveri`, `ArithmeticOrientationGeometry` | scaling surface, Hecke action, orbit rates; the window algebra is the Hecke action compressed to a window |

## 11. Success criteria and criteria for contributions

The programme succeeds when the questions of §5 have theorems as answers and the window `h¹` is
shown positive (or its carriers classified) uniformly along the tower, through one of: a Poincaré
inequality for the censored jump process against the end-profile potential at every length; a
positivity of the Jordan family surviving the derivative at `k = 0`; a count for the symmetric fold
masses compatible with the transitions.

A contribution must:
1. be a law along the tower (in `A`, in the level `N`, or across a stage), or a statement on one
   window that the tower structure turns into such a law;
2. say which part of the window it controls: the algebra (arithmetic), the archimedean jumps, the
   end profile, the pole plane;
3. say what it does on fakes (flip twins, Epstein data, golden curve);
4. be an identity or a structural inequality, not an estimate losing a factor growing with `A`;
5. be unconditional; equivalences with RH are labelled as such.

## 12. Big picture

A window of length `A` is a module over a finite local algebra: the Dirichlet ring truncated at
`e^A`. The tower is a chain of small extensions, one new fold per integer, generated by the primes.
Weil's window form is the archimedean jump form plus the logarithmic derivative of the window zeta
operator plus the pole plane; the same derivative, taken in the dimension of punctured affine
space, turns the Tate pieces of the degeneration into Weil's form. The tower's negativity grows at
most like `e^{A/2}` and at least like `e^{(zero width)·A}`. What remains is the positivity along the
tower: a Poincaré inequality against one universal end profile, or a count that pays the
symmetric fold masses compatibly with the transitions.
