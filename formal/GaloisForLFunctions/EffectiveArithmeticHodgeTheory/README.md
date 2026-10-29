# Effective Arithmetic Hodge Theory of the Multiplicative Group of `ℚ` (EAHT)

Namespace `GaloisForLFunctions.EffectiveArithmeticHodgeTheory`; umbrella `EffectiveArithmeticHodgeTheory.lean`.

**One sentence.** RH is the Hodge index theorem of an arithmetic surface whose points are the primes
with residue size `log p`, whose Frobenius is the Hecke ring of `ℚ_{>0}` together with the successor
`n ↦ n + 1`, whose cohomology is measured by log-volumes and log-orders of finite groups rather than by
dimensions, whose genus is infinite and whose boundary is the archimedean place. EAHT is the theory of
that surface **at finite height**: every statement names a height `T`, a length `N`, an overlap `c` or
an aperture, and passes to the limit in a topology that carries the index.

**Order of work.** Index, then count, then sign. The index is a global invariant of one Hermitian
kernel on `ℚ_{>0}`; a count (a one-sided bound at square-root precision) bounds it; positivity is the
last step, not the first.

Everything is unconditional; RH appears only inside equivalences.

---

## 1. Why a new field

### 1.1 The walls are one input

The corpus has reduced every route to the same obligation and proved that it cannot be avoided. Any
property of the prime-side source that implies RH is **parity-breaking** (it fails for the Liouville
twin `λΛ`), **square-root precise** (it fails for `Λ + εn^{−η}`, `η < ½`), **aperture-unbounded** (it
is not determined by any finite window) and acts at the
**ring level** (it fails for over-regular Beurling systems and for the golden datum `1 − 5X + 5X²`,
which share positivity, an Euler product and the right normalization). This is the deciding-input
theorem of [ASRP](../ArithmeticOfSquareRootPrecision/README.md). The same input appears in every
currency the corpus uses:

| Currency | The one input | Chapter |
|---|---|---|
| Count | `ψ(x) − x ≤ C√x log²x` eventually; one side suffices | ASRP, HKT |
| Parity | upper count of the odd Liouville class at square-root precision | AKL |
| Index | `κ(K_ζ) = 0` for the Weil kernel on `ℚ_{>0}` | HKT |
| Positivity | atomic Weil positivity at overlap `c_N → ∞` | TM, SSHA |
| Integrality | the Siegel or Liouville half of `{∫₀¹P} = lcm(1..n+1)^{−1}ℤ` at square-root scale | ASRP |
| Effectivity | `log|ℤ/lcm(1..N)| = χ(√N·A) + O(√N log²N)` | AET |
| Heat | collision mass `< 2` | HKT |

As properties of weights these are not equivalent. The count's stabilizer is the square-root class
`𝒬 = {δ : Σ_{n≤x} δ(n) = O(√x log²x)}`: every finite set of prime flips, `Λ + 1/n` and every
Euler-factor deletion of square-root mass lie in it (`count_signGauge_of_finite`,
`count_and_not_towerIndexZero_add_inv`). Tower positivity for all `C²` generators along one prime
holds for `Λ + δ` iff RH and `δ = 0` on `n ≥ 2` (`towerIndexZero_add_iff`). A count route works
modulo `𝒬` and need not reject a finite flip; only a full-positivity claim must see it. Two primes
are sufficient, not necessary: any two-prime lattice carries the index because it contains fine
towers, and all generators on one prime tower already decide RH. Selection must be proved in
positivity language; a producer is most naturally built in count language.

### 1.2 The walls as questions

- **W1 (selectivity).** Which property of `Λ`, absent from every bounded twin, bounds a signed
  arithmetic form at square-root precision on an unbounded family?
- **W3 (transfer).** In which topology does a sign or an index survive overlap growth, aperture growth
  and conductor growth, and which exhaustion carries the arithmetic point with it?
- **W14 (production).** Which independently built structure *produces* a one-sided count, as
  Riemann–Roch plus Stepanov produce it over `𝔽_q`?

Existing fields answer shadows of these questions. Analytic number theory answers them with `o(1)`
relative precision, and the corpus proves that is not enough. Algebraic geometry answers them over
`𝔽_q` with a surface, a Frobenius and sections. Krein–Langer theory answers W3 on `ℤ` and `ℝ`, not on
`ℚ_{>0}` with its towers. Transcendence theory produces auxiliary functions with multiplicity but has
never produced a prime count. EAHT is the field in which these four meet.

### 1.3 Why "effective"

Three facts force every statement to carry its scale.

1. **Finite index is Lindelöf-deep.** Finitely many off-line zeros forces the zeros to approach the
   line, hence LH and a fixed strip (HKT). A claimed index bound without its height is unfalsifiable;
   with its height it is checked against LH.
2. **The receivers are complete but not uniform.** RH is eventual positivity of the atomic family of
   one profile at overlap `c_N → ∞`, at a rate set by the profile's regularity: `C²` profiles need
   `c_N^{−2} log N → 0`, Gevrey-`s` profiles `c_N ≫ (log log N)^s` (SSHA), the
   Steklov–Denjoy–Carleman profile `c_N = (log log N)(log log log N)^β`, `β > 2` (TM). Positivity
   is proven at every fixed overlap `c < 1 + δ_*`, `δ_* = 1/107520002048050000`, for the plateau
   profile (TM, `eventually_completeWeilMatrix_posDef_certified`); `δ_*` is the boundary of the
   certificate, not a transition. Positivity and the sharp receiver use different profiles, so a
   signed transfer between profiles is part of every schedule statement. The whole problem lives in
   the sliver between the two, and only an effective statement can say where in it one stands.
3. **The coordinates are one.** An atomic test `f_x = Σ_{n≤N} x_n g((u − log n)/w)` with `w = c/N`
   has Fourier transform `w ĝ(wt) D_x(it)`, `D_x` a Dirichlet polynomial of length `N`; the window
   `ĝ(wt)` cuts the height at `T ≍ N/c`. Overlap `c` at horizon `N` is length `N` at height `N/c`,
   bandwidth `λ = log N/log T = 1 + log c/log T`. The square-root threshold `N = T` is the
   Montgomery–Vaughan diagonal, the density-hypothesis threshold, the Metzler threshold `c = 1` and
   the aperture `a = L/2` at once. RH sits between length `(1 + δ_*)T` and length
   `T (log log T)(log log log T)^{2+}`. In the Lean statements `c = Nw`; the exact spacing of
   `{log n}` at `N` is `log(1 + 1/N)`.

---

## 2. Point of view: the surface of `𝔾_m(ℚ)`

| Weil over `𝔽_q` | EAHT object | Over `ℤ` |
|---|---|---|
| curve `C`, surface `C × C` | the scaling surface: pole plane `⟨H, V⟩` plus test classes | ACS, AOG |
| Frobenius `F` | Hecke translations of `Γ = ℚ_{>0} ≅ ⊕_p ℤ`, plus the successor | towers `⟨p⟩`, consecutive ratios `⟨(n+1)/n⟩` |
| closed point of degree `d` | local constituent on a tower | `log p·δ₀ − L_p`, residue size `log p` |
| `H¹`, eigenvalues `β_i` | characters `u ↦ u^{ρ−½}` of `Γ`, points of the prime torus `𝕋^P` | zeros of `ζ` |
| `h⁰`, `χ = ½D·(D − K) + χ(𝒪)` | log-volumes, log-orders; box class `√N·A`, `χ = N` | `ψ(N) = log|ℤ/lcm(1..N)|` |
| genus `g`, Riemann–Roch `κ ≤ g` | infinite genus; no local ceiling | AKL zero-or-infinity law |
| Hodge index on `NS(C × C)` | negative index `κ` of the Weil kernel `K_ζ` on `Γ` | HKT |
| `N_m ≥ q^m + 1 − Cq^{m/2}` | the global law, a one-sided count | `ψ(x) − x ≤ C√x log²x` |
| Stepanov's auxiliary | a producer on the point side | open |
| quadratic twist, base change | the Liouville twin; towers and sublattices | AKL |
| degree of a point | height `T`, length `N`, overlap `c` | the effective coordinates |

**What is effective here.** Over `𝔽_q` every object is finite and the Hodge index is a statement about
a finite lattice. Over `ℤ` the objects are infinite, and EAHT replaces them by their finite sections:
the height-`T` part of the spectrum, the length-`N` part of the group ring, the overlap-`c` atomic
families, the box of side `H` in a two-prime lattice. A theorem of EAHT says what each section
carries, with explicit dependence, and in which topology the sections converge to the whole.

---

## 3. Objects

| Object | Role | Where it is built |
|---|---|---|
| Hermitian kernels on `Γ = ℚ_{>0}`, towers `⟨u⟩`, the negative index `κ`, hyperbolic pairs | the Hodge index as a Krein–Langer index | HKT, AKL |
| the Weil kernel `K_ζ(u) = W(g, g(· − log u))` of the cubic spline; its height truncations | the arithmetic instance | HKT |
| the **height filtration** `κ_T`: right zeros with ordinate `≤ T` | the effective index | this folder |
| towers of `Γ` as sampling grids; aliasing; the Nyquist window `2π/log u` | what a cyclic section carries | HKT, AKL, this folder |
| atomic families `Σ_{n≤N} x_n g_w(u − log n)` at overlap `c = Nw`; their Weil Gram matrices | the length-`N` sections | SSHA, TM |
| the **bandwidth dictionary** `(N, T, c, λ)` | the effective coordinates | this folder |
| precision classes of weights; the square-root class `𝒬`; the battery | the admissibility calculus | ASRP |
| the group ring `ℤ[Γ]`: integer Dirichlet polynomials, the integrality lattice, the Bézout ledger | sections and auxiliaries | ASRP, AKL, AET |
| the characteristic circle `μ_∞`, torsion orbits, log-orders as intersection numbers | the only integral intersection theory over `ℤ` | AIT, AET |
| regulators, counterterms, anomalies, survival cones | renormalization of the divergent diagonal | RAPT, RBG, AIT |
| the battery: Liouville twin, `cΛ`, flips, `Λ + εn^{−η}`, golden datum, over-regular Beurling systems, Davenport–Heilbronn | what every sufficient statement must fail | HKT, ASRP |

---

## 4. Language

**Index.** *Negative index* `κ(k)`: supremum of negative squares of the Gram matrices of `k`.
*Hyperbolic pair*: `ωχ + ω̄χ†` with `χ` non-unitary, one negative square. *Krein–Langer class*:
positive definite plus finitely many pairs. *Aliasing on a subgroup*: two pairs with equal
restrictions, or a pair becoming unitary. *Index-carrying topology*: one in which bounded index passes
to limits (pointwise convergence of kernels).

**Effective coordinates.** *Height* `T`: the ordinate window of the spectrum. *Length* or *horizon*
`N`: the support `{1, …, N}` of an atomic family, the length of its Dirichlet polynomial. *Overlap*
`c = N·w`: the number of neighbouring atoms an atom of width `w` meets near the top of the horizon.
*Bandwidth* `λ = log N/log T`. *Height filtration* `κ_T`: the number of right zeros of ordinate at
most `T`; `κ = sup_T κ_T`. *Section*: a finite family (tower window, box, atomic family) and the
Gram matrix the kernel induces on it. *Carries `m`*: the section's Gram matrix has at least `m`
negative squares. *Certifies height `T`*: carries every right zero of ordinate at most `T`.

**Exhaustion.** *Schedule*: a choice of section for every `N` (width `w_N`, overlap `c_N`). *Reaches
the index*: the indices of the sections converge to `κ`. *Decides RH*: positivity of the sections
eventually is RH. Reaching the index is stronger than deciding RH.

**Arithmetic.** *Producer*: a construction yielding a count without assuming it. *Receiver*: a
statement equivalent to a count. *Point side*: objects vanishing at primes (rational points). *Zero
side*: objects vanishing at zeros. *Selective*: fails for some bounded twin. *Precision class*: the
perturbations of the weight a statement survives. *Structure ladder*: sign, support (Euler product),
normalization (pole and Gamma), ring (additive relations).

**Every statement names** its height, length or overlap, its aperture, its conductor, its test class,
its norm, and what it gives over `𝔽_q`, on the golden datum and for the Liouville twin.

---

## 5. Foundational principles

1. **Irreducibility.** A sufficient input is parity-breaking, square-root precise, aperture-unbounded
   and acts at the ring level. A statement that survives a battery move is a dictionary entry, not a
   theorem.
2. **Structure, not estimate.** Precision is kept by identities, counts and self-dualities and lost by
   extraction (inversion, ceilings, majorants). A positive part never pays a hyperbolic pair.
3. **Index first.** Compute or bound the index from local constituents and one global law; positivity
   follows. Finite index is Lindelöf-deep: every claimed index ceiling must imply LH.
4. **Point side.** Producers vanish at the primes; zero-side annihilation certifies nothing.
5. **Effectivity.** Every statement carries its scale. A section is judged by what it carries at that
   scale and by the topology in which the sections converge.
6. **Calibration.** Reproduce Weil over `𝔽_q` by counting; fail on the golden datum, the complex fake
   and over-regular Beurling systems; recover PNT, Vinogradov–Korobov and Guth–Maynard in the field's
   coordinates.
7. **Renormalization carries its anomaly.** Positivity passes a scale limit exactly on the null cone of
   the counterterm; covariance is proved, not assumed.
8. **One arithmetic point.** Multiplicative data see a gauge orbit; the arithmetic point is
   distinguished only by additive relations (successor, Bézout, cells).
9. **Target-dependent precision.** A count theorem works modulo `𝒬`; a complete positivity theorem
   sees every coefficient; a census pays an aggregate exceptional budget. No tolerance is imported
   from one target into another without a proved bridge.
10. **Completion before sign.** The decisive estimate keeps both poles, the mixed blocks and the
    parity until their cancellation has been used. When a block `D > 0` is paid, what remains is the
    Schur complement `A − BD^{−1}B^*`, and a scalar positive symbol does not pay it.

---

## 6. Mechanisms

Imported from the chapters (proved there):

1. **Index formula and growth.** A positive-definite kernel plus `J` separated hyperbolic pairs has
   index `|J|`; along a separating element the kernel grows at the rate of the deepest pair, and a
   bounded positive part never pays a pair (HKT).
2. **Aliasing and Nyquist.** The tower `⟨u⟩` samples ordinates at spacing `2π/log u`; two right zeros
   alias on it iff they have equal real parts and ordinates differing by a nonzero multiple of
   `2π/log u`; a pair of distinct zeros aliases at most at one prime; two primes never alias (HKT,
   AKL).
3. **Receivers are bounded by the index.** Every Weil Gram matrix of real shifts of a `C²` compactly
   supported real test has at most `κ(K_ζ)` negative squares, at every width (HKT).
4. **Synthesis.** Euler–Maclaurin sums of a dilated Gevrey profile at the atoms `log n` reproduce a
   fixed Gevrey test up to an error whose Weil energy tends to zero when the overlap beats
   `(log log N)^s`; compactly supported profiles exist exactly above Gevrey class one (SSHA, HKT).
5. **The Bézout ledger.** Multiplicity times counted mass is at most size, in `𝔽_q[X]` and in `ℤ`;
   binomial auxiliaries vanish simply above `√N`; divisibility does not see parity (AKL).
6. **Precision.** The count's stabilizer is the square-root class; every error law weaker than square
   root is inherited by a weight failing the count (ASRP).
7. **Cyclotomic floor and affine windows.** For `m > 1` the primitive-root prefix energy
   `P_m(k) = Σ_ζ |Σ_{j<k} ζ^j|²` is at least `φ(m)` whenever `m ∤ k`, because a nonvanishing prefix
   is a nonzero cyclotomic integer whose norm has modulus at least one; the interpolant
   `A_m(k + u) = (1 − u)P_m(k) + uP_m(k + 1)` satisfies `A_m(t)/φ(m) ≥ {t}(1 − {t})`, uniformly in
   the conductor. Affine prime windows realize the unit average:
   `Σ_{AN<k≤BN} Λ(k)c_q(kn + h)/k → (log B − log A) c_q(n)c_q(h)/φ(q)`. Growing Ramanujan packets
   on `(A, 2A]`, `A ≥ 4Q(Q − 1)`, have frame bounds `1/4`, `5/4`, and the prime kernel compressed to
   one annulus is zero: the arithmetic transport lives between annuli (CACT).
8. **Non-ratio lags.** At width `c/N` the prime side of an atomic test is a lag form over the pairs
   `(n, kn ± r)`, `k ≥ 2`, `r < ckn/N` (SSHA); at `c = 1` only the boundary star `(N, N + 1)`
   enters and it vanishes after normalization (CACT). At `c = 3/2` the shells `r = 1` with
   `kn ∈ (2N/3, N]` enter, at `c = 2` those with `kn ∈ (N/2, N]`.

Proved in this folder: §7.2.

---

## 7. Pillar theorems

### 7.1 From the chapters

The index formula, closedness, the aliasing law, the arithmetic index formula, two-prime finiteness,
the Lindelöf law, height truncations and integer families carrying the index, the uniform receiver
bound (HKT); the tower Hasse principle, the zero-or-infinity law, the wave formula, the parity form of
the global law, compressions are receivers, the Bézout ledger (AKL); the stabilizer law, the
deciding-input theorem, the integrality exponent, the Baker separation of prime logarithms (ASRP);
Weil's argument as a growth law, the integer of the sign (AET); log-orders as intersection numbers,
the regulator anomaly (AIT).

### 7.2 Of this folder

- **B. The Hasse principle with heights** (`TheHassePrincipleWithHeights`). The height filtration
  `κ_T = #{ρ : Re ρ > ½, |Im ρ| ≤ T}` is finite, monotone, at most `2N(0, T) + c₀`, and exhausts the
  index: `κ(K_ζ) = sup_T κ_T` (`negIndex_zetaKernel_eq_iSup_heightIndex`). On a tower of scale `ℓ`
  with `ℓT < π` no two points of ordinate at most `T` alias, and `π` is sharp
  (`injOn_frobEig_of_mul_lt_pi`, `exists_alias_of_pi_le`); such a tower has a window carrying `κ_T`
  negative squares of the prime-side Gram matrix (`exists_window_certifies_height`). The tower of
  `3^k/2^j` with `k ≤ ⌊T log 2/π⌋ + 1`, `k ≤ j ≤ 2k`, `0 < |log(3^k/2^j)| < π/T`, certifies height
  `T` with a generator of logarithmic height `O(T)` (`twoPrime_tower_certifies_height`). At most
  `binom(κ_T, 2)` prime towers fail to separate the right zeros below `T`, so among any
  `binom(κ_T, 2) + 1` primes one tower carries them all (`ncard_heightBlindPrimes_le`,
  `exists_prime_certifies_height`).

Targets:

- **A. Effective completion.** The atomic families of the proven receiver schedules (Gevrey-`s`
  profiles at `c_N ≫ (log log N)^s`; the Steklov profile at `(log log N)(log log log N)^β`,
  `β > 2`) reach the whole index: their indices are at most `κ(K_ζ)` at every `N` and eventually
  at least every `m ≤ κ(K_ζ)`; the slowest schedule that reaches it; a signed transfer between the
  plateau and the Steklov profile.
- **C. The bandwidth dictionary.** The Fourier transform of an atomic family is the profile window
  times a Dirichlet polynomial of length `N`; overlap `c` at horizon `N` is height `N/c`, with the
  normalization of the critical-line evaluation fixed.
- **D. Arithmetic Stepanov at its ceiling.** What auxiliaries certified by a sup norm can reach, and
  what multiplicity a size-controlled integer auxiliary can carry; the joint inversion of the
  Stirling triple `(F, G, h)` of `log⌊y⌋! = F + G + h` beyond the sum of its separate bounds.
- **E. The completed shell symbol at a macroscopic overlap.** At `c = 3/2` or `c = 2`, the action of
  the finitely many successor shells on growing Ramanujan packets, computed through the affine unit
  averages and the exact divisor jet with prime, Robin, Gamma and both poles combined before any
  remainder is estimated; whether it contains `∫ A_m(t)/φ(m) dν(t)` with `ν ≥ 0`; the Schur cost of
  the paid additive block; a full-matrix lower bound for one fixed full-support profile.
- **F. The flip threshold.** For the remote flip `ω_p`, `p ≥ 11` (hyperplane gap exactly `2 log 2`,
  complete positivity false), the least overlap `c*(p)` at which the complete atomic form separates
  `ω_p` from `Λ`: the scale at which selectivity first appears in the finite sections.

---

## 8. Traps

| Trap | Truth |
|---|---|
| Deciding RH is reaching the index | A schedule can decide `κ = 0` and still undercount `κ`; reaching is the stronger statement |
| One prime certifies every height | One prime tower aliases; the Diophantine question is which prime, and fine towers inside `⟨2, 3⟩` certify height `T` explicitly |
| Bounded overlap suffices | A tempered single-pair configuration is negative at every fixed overlap; the overlap must grow, and the Weil kernel's density is what makes growth work |
| A finer prime-side statement separates `ζ` from twins | Sign twins have congruent atomic prime forms; selectivity lives in the pole and the archimedean place |
| Local positivity sums | Each constituent is positive definite up to its identity term; finitely many places have index `0` or `∞` |
| Integrality reaches only linear precision | The floor is exact; what is linear is the ceiling used to certify auxiliaries |
| A new equivalence is progress | The receivers are complete; a contribution computes, bounds or structures the index at a stated scale |
| Finite index is a sub-Lindelöf target | Finite index forces LH |
| A count route must reject finite flips | Every finite flip set lies in the count's stabilizer `𝒬`; only a full-positivity claim must see a flip |
| Positivity at every fixed `c` gives positivity along `c_N → ∞` | The horizon `N₀(c)` may grow faster than any schedule; bounded-overlap completeness is not established |
| The proven positivity and the sharp receiver share a profile | Positivity is proved for the plateau, the sharp receiver for the Steklov profile; a signed transfer is needed |
| A scalar positive symbol pays the shells | After the paid block the form is a Schur complement; cross-mode and cross-annulus terms are part of one operator |

---

## 9. Questions the programme answers

1. **W3: in which topology do sections carry the index, and how fast must the schedule grow?**
2. **Hasse principle with heights: which section certifies all zeros of height at most `T`?**
3. **Bandwidth: how do overlap, length and height translate, and where is the threshold?**
4. **W14: what can an auxiliary over `ℤ` certify, and where is precision lost?**
5. **W1: which statements of the theory are selective, and at which scale does selectivity first
   appear?** In the finite sections: the flip threshold `c*(p)`.
6. **Converse Krein–Langer on `Γ`: is finite index a Krein–Langer decomposition for every kernel?**
7. **W1 at macroscopic overlap: does the completed successor-shell symbol at `c = 3/2` or `2` carry
   the cyclotomic floor with nonnegative weight, and what pays the Schur cost?**

---

## 10. Tools

To build: effective index carriers for finite exponential sums; bilinear continuity of Weil's form
in the Lévy norm and Gram-matrix convergence of synthesized families; the bandwidth dictionary; a
signed symbol calculus for the completed shell operator on Ramanujan packets, with composition and
elimination rules that keep the Schur cost; the flip test on the atomic complete form; constrained
inversion of the factorial identity; ceilings for integer auxiliaries.

Built: certifying towers of given height in `⟨2, 3⟩` (`TheHassePrincipleWithHeights`).

---

## 11. Open research topics

1. **Converse Krein–Langer on `Γ`.** A common invariant negative subspace for all prime translations of
   the Pontryagin space of a finite-index kernel.
2. **Arithmetic Stepanov.** Auxiliaries in `ℤ[Γ]` with `p`-adic multiplicity; an arithmetic zero
   estimate; the flatness identity playing `x^q = x`; the odd-class upper count at a power precision.
3. **Quadratic Riemann–Roch on the scaling surface.** A section count of box-class size `N` defined
   without the sign, with Riemann inequality and subquadratic degree-zero growth.
4. **Covariant regulators on the characteristic circle.** A regulator of the diagonal with nontrivial
   null cone; Riemann–Roch on torsion orbits with defect `½ log|d|`.
5. **Index-carrying completion with explicit schedules.** The slowest schedule that reaches the index;
   arithmetic synthesis (Möbius or Ramanujan cell weights) below the quasi-analytic rate; signed
   transfers between profiles.
6. **Local-to-global with heights.** Explicit certifying primes; locality when the depth supremum is
   not attained.
7. **Geometry of the parity twin over `ℤ`.** The object whose base changes produce the Liouville twist.
8. **Arithmetic Herglotz theory.** Positive measures from primes and the successor whose moments are
   explicit-formula values.
9. **Infinite symmetry.** Polar divisors of positive-genus affine Eisenstein series.
10. **Depth-sensitive census.** Observables sensitive to displacement at depth `1/log T` with prime-side
    upper bounds.
11. **Macroscopic overlap and the Schur cost.** The completed shell symbol at `c = 3/2` and `c = 2`;
    the residual after the cyclotomic floor; the overlap dependence of the reserve.
12. **Constrained inversion.** Precision from the relations among the Stirling terms `F, G, h` rather
    than from a norm bound on each; the precision at which the sawtooth cancels against `μ`.
13. **Selection and invisible perturbations.** What each observable determines: the count modulo
    `𝒬`, tower positivity everything, fixed-overlap complete forms up to the flip threshold.

---

## 12. Place in the research

EAHT is the field whose chapters already exist in the corpus; this folder holds the effective chapter
and the theorems that tie the chapters together.

| Programme | Chapter | Interface |
|---|---|---|
| [HeckeKreinToeplitz](../HeckeKreinToeplitz/README.md) | I. Index | kernels, index formula, receivers, height truncations, the Weil kernel |
| [ArithmeticKreinLangerTheory](../ArithmeticKreinLangerTheory/README.md) | II. Local to global | Hasse principles, fine towers, parity form, Bézout ledger |
| [ArithmeticOfSquareRootPrecision](../ArithmeticOfSquareRootPrecision/README.md) | III. Precision | stabilizer, deciding input, integrality lattice, Baker separation |
| [ArithmeticEffectivityTheory](../ArithmeticEffectivityTheory/README.md), [ArithmeticIntersectionTheory](../ArithmeticIntersectionTheory/README.md) | IV. Sections and intersections | effectivity functions, log-torsion, torsion orbits, anomaly |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md), [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | V. The surface | scaling surface, tower laws, orbit correlations, golden datum |
| `SpacingScaleHarmonicAnalysis`, `TransMetzlerWeilPositivity` | VI. Overlap | atomic families, synthesis, positivity at touching and below `1 + δ_*`, non-ratio lags |
| `CriticalArithmeticCorrelationTheory` | VII. Finite-horizon correlation | cyclotomic floor, affine prime windows, annular frames, divisor jet, boundary star |

---

## 13. Success criteria and what a contribution is

**Success.** The three walls become three theorems about finite sections of one kernel: a transfer
theorem reaching the index along an explicit schedule (W3); the complete form positive at one
macroscopic overlap with the flip threshold computed (W1); and a produced count at some power
precision for one parity class (W14), which by the parity form of the global law and the integrality
exponent is a zero-free strip. The section certifying every zero below a given height, with explicit
size, is proved.

**A contribution** is an unconditional theorem that names its scale (height, length, overlap,
aperture), its section and its topology; computes, bounds or structures the index there; says what it
gives over `𝔽_q`, on the golden datum and for the Liouville twin; and records the positive survivor of
every no-go. A new equivalence without a scale is not a contribution.
