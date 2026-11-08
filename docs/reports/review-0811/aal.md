# The asymptotic abscissa law (AAL)

This report covers:
- what AAL says and its exact Lean forms;
- what a proof or a disproof would have to establish;
- everything the corpus has proved around it, including its finite case;
- the models it must defeat, the approaches that fail and why;
- the open problems and the milestone toward it.

Statements called *proved* are theorems of the Lean corpus (commit `48ce5506c8` plus the working tree of 2026-11-08). *Classical* marks results from the literature that are not formalized here, *heuristic* marks unproved expectations, and `[D]` marks a deduction that is not a Lean theorem. Section 13 says where each result lives in Lean.

---

## 1. The problem

### 1.1 Notation

**Zeros and abscissae.**
- Zeros are the nontrivial zeros `ρ = β + iγ` of `ζ`, counted with multiplicity.
- `Θ = sup Re ρ` is the zero abscissa.
- `Θ∞ = inf{σ ≥ ½ : only finitely many zeros have Re ρ > σ}` is the asymptotic abscissa: `σ ≥ Θ∞` exactly when all zeros above some height have `Re ρ ≤ σ`, so `Θ∞` is the limit superior of `Re ρ` as `|γ| → ∞`.
- `Θ₂ = sup({½} ∪ {Re ρ : Re ρ < Θ})` is the second abscissa.
- Always `½ ≤ Θ∞ ≤ Θ ≤ 1`.

**Hypotheses.**
- **ZAL** (zeros approach the line): `Θ∞ = ½`, i.e. finitely many zeros beyond every positive depth.
- **qRH** (quasi-RH): `Θ < 1`.
- **FOL** (finite off-line support): finitely many off-line zeros.

**Tops.**
- A *right zero* has `β > ½`; the *top layer* is the set of zeros with `β = Θ`.
- The top is *attained* if some zero has `Re ρ = Θ`.
- **NAT** (no attained top): no zero attains a maximal real part above `½`. Equivalently: RH holds, or the supremum `Θ` is not attained.

**Functions and kernels.**
- `ψ` is Chebyshev's function; `Φ(L) = Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))` is the Weil lag function, which is real.
- `E_y = Π_{p≤y}(1 − p^{−s})^{−1}` is the Euler head, `M_y = 1/E_y`, and `ζM_y` is the Euler tail.
- `K_ζ(u) = W(B, B(·−log u))` is the Weil kernel of the cubic spline `B` on the Hecke lattice; `κ(K_ζ)` is its negative (Krein–Langer) index.
- `ξ(s+a)ξ(s−a)`, `a ≥ 0`, is the symmetric shift of `ξ`.

### 1.2 The statement

> **AAL.** `Θ∞ = Θ`.

Each of the following is equivalent (proved):
1. For every `h ≥ 0`: if only finitely many zeros satisfy `Re ρ > ½ + h`, then none does. This is the formal definition.
2. For every `σ ≥ ½`, the set of zeros with `Re ρ > σ` is empty or infinite.
3. For every `σ < Θ`, infinitely many zeros satisfy `Re ρ > σ`.
4. For every right zero `ρ` and every `r > 0`, infinitely many zeros satisfy `Re w > Re ρ − r`.
5. **Eventual-to-global.** For every real `σ`: if every zero above some height has `Re ρ ≤ σ`, then every zero has `Re ρ ≤ σ`.

AAL says nothing about the value of `Θ`. It allows `Θ = 1`, and it allows the top to be attained or not.

**Form 5 is the working form.** AAL turns a bound that holds for all but finitely many zeros into a bound for all zeros. It is a self-improvement law in the exceptional-set coordinate, not a statement about the location of the line (section 2.2).

### 1.3 The negation

> **¬AAL.** Some `σ ≥ ½` has finitely many, and at least one, zeros with `Re ρ > σ`. Equivalently `Θ∞ < Θ`.

So `ζ` has a finite top layer of zeros, separated by a gap from all the others. The top is attained by finitely many zeros. Its full structure is section 4.

### 1.4 What proving and disproving mean

**Proving AAL** means proving one of the forms in 1.2 or section 2 for the actual `ζ`, or the hypothesis of any implication in section 5. Assuming that hypothesis proves nothing: it is the open mathematics.

**Disproving AAL** means producing:
- abscissae `½ ≤ β₁ < β* < 1` and a height `T*`;
- a finite nonempty layer of zeros on `Re s = β*`;
- a proof that every zero above height `T*` lies in `1 − β₁ ≤ Re s ≤ β₁`.

The last item is a zero-free region of quasi-RH type at all large heights. A disproof therefore refutes RH and proves quasi-RH at once. It cannot be a computation.

The expected answer is that AAL holds.

### 1.5 Where AAL sits

| | ZAL (`Θ∞ = ½`) | not ZAL (`Θ∞ > ½`) |
|---|---|---|
| **AAL** | RH | RH fails; off-line zeros at unbounded heights with real parts accumulating at `Θ = Θ∞`; no finite top; `Θ = 1` not excluded |
| **not AAL** | finitely many zeros beyond each positive depth and a finite top at `Θ < 1`; includes the finite stratum (FOL) | a finite top layer above an infinite population accumulating at `Θ∞ ∈ (½, Θ)` |

Proved relations:
- **RH ⇔ ZAL ∧ AAL.** ZAL makes the zeros right of `½ + h` finitely many, and AAL then makes them absent.
- **RH ⇒ AAL**, trivially. **¬AAL ⇒ qRH ∧ ¬RH**, so **qRH or AAL** always holds.
- **ZAL ⇒ qRH.** Under ZAL, ¬RH forces an attained top, so under ZAL the statements AAL, NAT and RH coincide.
- **AAL ⇒ B13** (FOL ⇒ RH), strictly: B13 is AAL at the single abscissa `σ = ½` (section 2.3).

AAL implies no zero-free region. It is strictly below RH, independent of quasi-RH in the known sense, and together with ZAL gives RH. It is false on several fake zeta functions (section 6), and its negation is one rigid object (section 4).

### 1.6 Where AAL sits in the curve proof [D]

The corpus proves RH for every hyperelliptic curve over a finite field of odd characteristic in three steps: a crude count at every level of the base-change tower (Stepanov's auxiliary polynomial), self-improvement of any constant-factor bound to the sharp one by power sums, and the functional equation pinning every mode to the circle (proved). Over `ℤ` the crude count is ZAL, the self-improvement is AAL in form 5, and the functional equation is that of `ξ`. On a curve the self-improvement is algebra because the rank is finite; over `ℤ` the modes are infinite, a constant-factor crude bound `|ψ(x) − x| ≤ C√x` is false, and the self-improvement must act in the exceptional-set coordinate. AAL is therefore the infinite-rank analogue of power-sum elimination plus the functional equation.

### 1.7 Points that are easy to get wrong

1. **¬AAL does not mean finitely many off-line zeros.** Below `β₁` there may be infinitely many. FOL is the special case where the off-line zeros are exactly the finite layers.
2. **AAL does not mean infinitely many off-line zeros.** Under RH it holds with none. AAL together with ¬RH forces infinitely many.
3. **AAL is weaker than NAT.** AAL permits a top `Θ > ½` attained by one zero, provided infinitely many zeros have real parts in every interval `(Θ − ε, Θ]`.
4. **AAL does not single out the line.** Symmetric shifts move every zero by `±a`, keep the functional equation and preserve AAL (proved). An argument for AAL that uses the value `½` beyond the functional-equation involution and Hardy's zeros proves too much.
5. **The zero of maximal angle is not a sign of ¬AAL.** It exists whenever RH fails, in every world.
6. **A top layer is high.** No off-line zero has ordinate in `(0, 67]` (proved). Classically, RH is verified up to height `3·10¹²`.
7. **Integer norms do not protect AAL.** A Beurling system with integer norms, nonnegative natural coefficients, an Euler product and linear counting has exactly one off-line pair on `Re s > ½` (proved).

---

## 2. Equivalent forms

### 2.1 The list

AAL is equivalent to each of the following (proved):

1. **`Θ∞ = Θ`.**
2. **Eventual-to-global.** For every `σ`, a right bound valid for all zeros above some height is valid for all zeros.
3. **Eventual-to-global for a symmetric shift.** For any fixed `a ≥ 0`, the same law for the zeros of `ξ(s+a)ξ(s−a)`.
4. **No isolated spectral gap.** There are no `½ ≤ β₁ < β* < 1` and `T* > 0` with: no zero right of `β*`; a finite nonempty conjugate-symmetric layer on `Re s = β*` below `T*`, with its reflection on `Re s = 1 − β*`; the strips `(β₁, β*)` and `(1 − β*, 1 − β₁)` zero-free at all heights; every other zero in `[1 − β₁, β₁]`.
5. **The prime error is not a finite oscillation.** There are no `β > ½`, `η > 0` and nonzero finite real trigonometric polynomial `T` with `ψ(x) − x = x^β T(log x) + O(x^{β−η})`.
6. **No two-prime dilation annihilation.** For any two distinct primes `p ≠ q`, no finite frequency set `S`, `β ∈ (½,1)`, `η > 0`, with a zero right of `β − η`, makes both dilation combinations `Σ_k P_k ψ(x/p^k)` and `Σ_k P_k ψ(x/q^k)` — `P = Π_{ω∈S}(1 − 2b^β cos(ω log b)X + b^{2β}X²)` at `b = p, q` — reduce `ψ` to its linear main term up to `O(x^{β−η})`.
7. **Every right zero has infinitely many companions.** For every right zero `ρ` and every `r > 0`, infinitely many zeros satisfy `Re w > Re ρ − r` (transport form).
8. **Finite subtraction never lowers the lag exponent.** Removing the waves of finitely many zeros from `Φ` leaves growth exponent `Θ∞ − ½`; without subtraction it is `Θ − ½` (Landau). AAL says that subtracting finitely many waves never helps.

### 2.2 What shift invariance says

The zeros of `ξ(s+a)ξ(s−a)` are the translates `ρ ± a`; global bounds and bounds beyond a fixed height both move by exactly `a` (proved). So `ξ` satisfies AAL iff every symmetric shift does. The shifted products have the functional equation about `½` and an Euler product, and their zeros sit on `Re s = ½ ± a` under RH. Consequences [D]:
- AAL is a property of the configuration of zeros, invariant under rigid horizontal motion of all of them;
- the functional equation that a proof uses must act as an involution, not as a marker of the line `½`;
- `Θ < 1 ⇒ Θ = ½` (self-improvement of a strip) fails on the shifted products (proved), while AAL survives on them.

### 2.3 AAL at one abscissa: the finite stratum

At `σ = ½` form 2 reads "**RH above some height ⇒ RH**". The corpus proves that the following are equivalent (the finite stratum):
- `κ(K_ζ) < ∞`;
- `K_ζ` has finite index on the lattice of two primes `⟨p, q⟩`;
- FOL: finitely many off-line zeros;
- the heat flow has a uniformly bounded number of non-real zeros for `t > 0`;
- every zero above some height lies on the critical line;
- the Gaussian-filtered central gap is `O(√ε)` at every large height.

So **AAL at `σ = ½` is exactly B13: FOL ⇒ RH**. It is strictly weaker than AAL, which is the same law at every `σ`. In the corpus it is the milestone toward AAL (section 11).

---

## 3. What a proof of AAL would give

**Statements that collapse to RH.** Under AAL each of the following is equivalent to RH (proved):
- ZAL;
- FOL, and with it every member of the finite stratum of 2.3: finite `κ(K_ζ)`, finite index on one two-prime lattice, bounded heat counts, RH above some height, the eventual Gaussian central-gap budget;
- finite critical source energy;
- eventual Hadamard positivity;
- a finite-dimensional odd bound-state space;
- bounded Jensen non-real counts `N_d`.

**Large-height gauges.** Every large-height gauge reads `Θ∞`: eventual Hadamard positivity right of `½ + h` holds exactly when all zeros satisfy `Re ρ ≤ ½ + h`; the eventual central-gap rate equals the all-height rate; the optimal large-height Gaussian growth rate is `b∞ + b∞²/8` with `b∞ = Θ∞ − ½` (proved).

**Effect across the corpus.**
- Every programme whose large-height receiver delivers "all but finitely many" becomes an RH programme: finite index (HF, HKT, AKLT, CWS, SC glued index), bounded heat counts (ZCG, WD), bounded `N_d` (LA, FFP), eventual sign statements.
- Proving RH reduces to proving ZAL.
- The one-off countermodels stop being models of `ζ`, and the proof names the property of `ζ` that separates them.

**What AAL does not give.** No zero-free region and no ZAL. The remaining half, ZAL, is at least quasi-RH; in the curve picture (1.6) it is the crude count, which over `ℤ` is the harder step.

---

## 4. The world without AAL

Everything in this section is proved, and a proof by contradiction may use all of it.

### 4.1 The zero configuration

**The spectral gap.** There are `½ ≤ β₁ < β* = Θ < 1` and `T*`; a finite conjugate-symmetric top layer on `Re s = Θ` below `T*` with its reflection on `Re s = 1 − Θ`; zero-free strips `(β₁, Θ)` and `(1 − Θ, 1 − β₁)` at all heights; every other zero in `[1 − β₁, β₁]`. Also `Θ∞ ≤ Θ₂ < Θ`.

**The high zero-free region.** `ζ` is zero-free on `Re s > β₁, |Im s| > T*`; on discs at distance `δ` from the zeros `|(ζ′/ζ)^{(k)}| ≤ k! C log(t + r)/(δ r^k)`; derivative returns to the top layer can only occur at exponentially large heights. Classically the high zero-free region gives Lindelöf-type bounds right of `β₁`.

**Shift stability.** The world is carried by every symmetric shift to a world of the same type, with both layers moved by `±a`.

### 4.2 The prime error

**The finite oscillation.** `ψ(x) − x = x^Θ T(log x) + O(x^{Θ−η})` for every `0 < η < Θ − Θ₂`.

**Rigidity of the witness.** Exponent exactly `Θ`; frequencies exactly the ordinates `μ` of the top layer; coefficients exactly `−ord_{Θ+iμ}(ζ)/(Θ + iμ)`; zero constant mode; a unique profile `T`. No saving larger than `Θ − Θ₂`. Unconditionally, no finite oscillation approximates `ψ(x) − x` to `O(x^{σ₀})` with `σ₀ < ½`.

**Sign changes.** There are `L, δ > 0` such that every logarithmic window `[u, u + L]` far out contains points with `ψ(e^u) − e^u > δe^{Θu}` and points with `< −δe^{Θu}`.

**Power sums.** Turán's second main theorem, in separation-free form, applies to the top layer: on every window of `|G|` consecutive exponents some power sum of the normalized top phases is at least `1/(2e|G|(6(|G|+1)(M+2|G|+2))^{|G|})`; applied to all `ξ`-zeros with a finite head and tail bounds it gives an explicit lower bound for the full sum (proved). So `ψ(x^ν) − x^ν` is of size `≥ c x^{νΘ}` at some `ν` in every window of `|G|` geometric exponents.

**Parity transfer.** `Σ_{n≤x}(−1)^nΛ(n) = 2⌊log₂⌊x⌋⌋ log 2 − ψ(x)` exactly.

**Dilation annihilation.** At every base `b > 1` the combination `Σ_k P_k ψ(x/b^k)` annihilates `x^Θ T(log x)`, leaving `κ_b x + O(x^{Θ−η})`, `κ_b ≥ (1 − b^{Θ−1})^{2|S|} > 0`; one base confines every zero right of the error exponent to `Re ρ = Θ` and to lattices `α + (2π/log b)ℤ`; two prime bases make the layer finite.

**The top annihilator and the twisted functional equation.** `D(s) = Π_{ρ∈F}(1 − b^{ρ−s})^{m(ρ)}` vanishes on the top layer and is bounded away from zero on `Re s ≤ ½`; dividing `ξ` by the finite Blaschke product of the top layer twists `s ↔ 1 − s` by a nonconstant unimodular phase.

### 4.3 Jets at a rightmost zero

Let `ρ` be a top zero of multiplicity `m` and `a_{k,n} = Λ(n)(log n)^k/(k! n^{ρ+1})`. Then `Σ_n a_{k,n} → −m`; the diagonal `Σ_n |a_{k,n}|² → 0`; the off-diagonal `Re Σ_{n≠j} a_{k,n}\overline{a_{k,j}} → m²`, and this limit survives removing all shifts `h ≤ r^k` (`1 < R < Re ρ + ½`, `r < R²`) and every proper prime power. The distinct-prime pair source has double-pole coefficient `m²`; its simple coefficient is that of `(ζ′/ζ)²` plus `2mH(ρ)`, `H` the proper-prime-power tail. The obstruction lives in a long-shift correlation of the primes. Calibration: at `s = 2` the same sequence has moments `→ +1` with vanishing diagonal, so diagonal decay never excludes a nonzero moment. The jet argument uses only attainment.

### 4.4 Transport, returns and lags

**Returns near a top zero.** Every phase return has unbounded translates on every connected domain joining a top zero to `Re s > 1`; at aligned shifts `|ζ|` exceeds every polynomial in the aligned length on the disc about each top zero; returns of `ζ` to itself on a disc about a right zero are tail-bad at every cut and have density zero; under ¬AAL returns strong enough to move a zero have finite total measure.

**Lags.** For `a < Θ − ½` and every `M` the set `{L : Φ(L) > Me^{aL}}` has positive upper density; every lag progression `m ↦ Φ(mℓ)` is unbounded above.

**Spectral readings of the attained top.** The restricted Weil ground energy decays like `μ₀(B) ≤ −c e^{2(Θ−½)B}/B³`; `K_ζ` is bounded on only finitely many prime towers; an attained maximal depth is visible to a compact `C²` test (Cesàro extraction along a nonresonant grid).

### 4.5 The finite stratum

If the off-line zeros are finitely many and nonempty, in addition:
- **Krein–Langer structure.** `K_ζ = K_on + Σ_{ρ right} h_ρ`: the orbit kernel of the on-line zeros, positive definite, plus one hyperbolic pair per right zero. `κ(K_ζ)` equals the number of right zeros, is even, and is already attained on any two-prime lattice; RH ⇔ `κ ≤ 1`.
- **Lindelöf.** Finite index forces the zeros to approach the line, hence the Lindelöf hypothesis and a zero-free half-plane `Re s > ½ + α`, `α < ½`.
- **Towers decide.** At most `κ(κ−1)/2` primes are blind; every other prime tower carries the full index, and RH ⇔ the kernel on one non-blind tower is PD ⇔ infinitely many towers are PD [K].
- **Hodge violation at an explicit level.** With a gap `g` below the depth of one right zero, the Hodge index fails at every level `a ≥ (1/2g)log⁺((2M + 4Σ|q_t|)/c) + (|T| + 2)ℓ/2 + w`.
- **Defects decay.** Unit-window Hecke defects decay faster than every power of `T`, uniformly at aperture `c log T`.
- **The inner field** tends to zero on every vertical line right of `½`.
- **The explicit formula** is exact up to finitely many oscillating terms over an RH-size remainder: `ψ(x) − x = −Σ_{j≤k}2Re(x^{ρ_j}/ρ_j + x^{1−ρ̄_j}/(1−ρ̄_j)) + O(√x log²x)` [D].

### 4.6 What the world without AAL does not provide

- Finiteness of the off-line zeros in general.
- Simple zeros, or ℚ-linear independence of the top ordinates.
- Information about a second finite layer between `Θ∞` and `Θ`.

### 4.7 The precision of this world

**The unconditional limit.** `ψ(x) − x ≪ x exp(−c(log x)^{3/5}(log log x)^{−1/5})` (Vinogradov–Korobov).

**The precision of this world.** The prime error is a finite oscillation at size `x^Θ`, `Θ < 1`, with a power-saving remainder. No unconditional estimate of `ψ`, of the Mertens function or of the Liouville sum resolves `x^Θ`, so no such estimate distinguishes AAL from its failure.

**Where a contradiction can come from.**
1. Information valid at every precision. Exact identities are blind (section 7); what remains is positivity, integrality and discreteness — and positivity and integer norms are already carried by countermodels (section 6).
2. Unconditional power-saving inequalities for other objects: mean-value theorems for Dirichlet polynomials, the large sieve, Weil's bounds, Turán's power-sum lower bounds.
3. The regularity this world forces at large heights: the zero-free region and Lindelöf-type bounds right of `β₁`.
4. The functional equation acting on the finite top layer and its mirror — the one property no countermodel has (section 8.7).

---

## 5. What is known to imply AAL

Each implication below is proved. Each hypothesis is open for `ζ`.

### 5.1 Attainment: implications that prove NAT

**The common mechanism.** An attained top `ρ₀` carries a weight with `Re 1/(ρ₀(1−ρ₀)) > 0`. Dirichlet's theorem aligns the finitely many top phases, and a twist `1 + cos(γ₀L)` moves the weight to a real exponent; a one-round Landau theorem detects it. A non-attained supremum has no real point, which is why these arguments prove NAT, not RH.

| Hypothesis | Comment |
|---|---|
| `Φ(m log b)` bounded above along one geometric progression `b^m` | over a finite field this is Stepanov's argument along `qⁿ` |
| `Φ(mℓ)` bounded above along one arithmetic progression | RH ⇔ ZAL ∧ one bounded progression; RH ⇔ the set of good spacings is not meagre |
| integer lags bounded above on a logarithmically dense set of integers | power-saving gaps are RH-complete; sub-power gaps give only AAL |
| for every `a > 0`, `Φ(L) ≤ M_a e^{aL}` outside a set of finite measure, of Abel density zero, or of lower density zero | the lag form, 8.2 |
| subexponential lower bounds for the two-bump prime-window functional along one grid | at all real `v` it is RH |
| nonnegative twisted plateau Weil energies | — |
| JAS positivity: real-amplitude at level one; dressed at a level `σ ≤ 1`; typical at every level in `(½,1)`; constant-vector positivity on infinitely many dyadic prime shells (Turán power sums with a finite head) | — |
| `K_ζ` bounded, or PD, on infinitely many prime towers | — |
| bounded coupling of `K_ζ` on one positive two-prime cone | cannot select a zero width, but implies AAL |
| a subexponential lower floor for the restricted Weil ground energy | — |
| eventual nonnegativity of single-scale grid factorial-tent energies | — |
| every off-line zero strictly exceeded in distance from the line by another | a form of NAT |

### 5.2 Transport: implications that prove exactly AAL

**The common mechanism.** Phase returns `n^{−iτ_j} → 1` exist by Kronecker; translates of `ζ` converge to `ζ` on `Re s > 1`; a bound on translates near a zero gives convergence there (Vitali, three circles); Rouché copies the zero.

| Hypothesis | Comment |
|---|---|
| weak recurrence beyond every height for discs about right zeros | RH ⇔ ZAL ∧ weak recurrence about off-line zeros |
| infinitely many companions of every right zero | AAL itself (form 7) |
| a phase return with bounded translates on a domain joining each right zero to `Re s > 1` | every such domain lies in `Re s > ½` |
| **slow aligned returns right of the line** (B89): for each right zero `β + iγ`, `σ₀ ∈ [½, β)` and shifts `τ` with `n^{−iτ}` within `1/N` of `1` for `n < N`, arbitrarily large `N, τ`, and `|ζ(s + iτ)| ≤ N^A` on the disc about `3 + iγ` with left edge `σ₀` | explicit transport exponent; on discs crossing `Re s = ½` the hypothesis is RH |
| decay of the inner field on every vertical line, with weak recurrence about off-line zeros | equivalent to RH |

Transport is a reformulation: returns strong enough to move a zero are as rare as the zeros they move.

### 5.3 Implications for the finite stratum

Each proves B13 (FOL ⇒ RH), not AAL.

| Hypothesis | Comment |
|---|---|
| in the finite stratum, the kernel on one non-blind prime tower is PD | equivalent to RH there [K] |
| in the finite stratum, infinitely many prime towers are PD | equivalent to RH there [K] |
| a zero-or-infinity law for the negative index of `K_ζ`, or of its restriction to one two-prime lattice | equivalent to B13; such laws are proved for kernels with escape, mixing or slope-height decay and for tensor squares |
| `κ(K_ζ) ≤ 1` from any input | equivalent to RH (the index is even) |

### 5.4 Thin, thick and compressing receivers

A receiver decides RH when its test family is thick (an interval or non-meagre set of spacings, all heights, all prime sets in dyadic windows) or when its coordinate compresses height so that every top is attained, at a resolution cost. A thin family in a height-uniform coordinate sees only attained tops: it is worth NAT and needs a separate ZAL producer. AAL is the attainment gap of a coordinate, not of the zeros.

---

## 6. Models

### 6.1 Models that violate AAL

**Continuous Beurling one-offs.** For `1/3 < μ < 1/2`, `0 < ν < 3μ − 1`, `γ ≠ 0`: a continuous Beurling system with positive prime and integer densities, an Euler product, `N(x) = ρx + C + o(1)`, `ζ_B(σ + it) → 1` on vertical lines, and zeros right of `½` exactly `(1 − μ) ± iγ`. It satisfies ZAL and violates AAL. Lesson: positivity, an Euler product and an excellent count do not give AAL.

**A discrete Beurling one-off.** Primes `p_k = e^{t_k}` following the continuous density; the same pair right of `½`; the continuation blows up at `s = ½` because `Σ1/p_k = ∞`. Lesson: discreteness does not give AAL.

**An integer-norm one-off.** Integer labels `q_k ≥ 2` (repetition allowed), nonnegative natural coefficients, an Euler product, linear counting, holomorphic on `Re s > ½` away from `1`, with zero set there exactly `{3/5 ± iγ}`; the weighted prime count is `n + n^{3/5}Ω(log n) + O_ε(n^ε)`. Lesson: integer norms with positive generators and linear counting do not give AAL.

**A rational-prime one-off.** Rational-prime labels (repeated), multiplicative natural coefficients, linear counting, holomorphic on `Re s > 17/30` with zero set there exactly `{3/5 ± iγ}`. Lesson: labels that are rational primes do not give AAL either; what such a system lacks is continuation to the line with the functional equation.

**`ξ_β = (s − β)(s − 1 + β)ξ`.** Functional equation, order one, reality, Gamma factor, a real off-line pair implanted; no Dirichlet series. Lesson: functional equation, order and reality do not give AAL.

**Symmetric rational zero relocation.** It keeps the functional equation, reality on the line and the vertical asymptotics, and implants off-line zeros; it destroys Bohr almost periodicity and every Dirichlet-series representation on `Re s > 1`. With the multiplier normalized at `0` and `1`, relocating two critical pairs to `Re s = ¼, ¾` gives a signed, integrable, zero-mass Dirichlet density, negative on `(1, 1 + ε)` under every finite Dirichlet filter. Lesson: a top layer cannot be put into `ζ` by surgery that keeps positive coefficients.

**Heat deformations.** If RH fails, `Λ > 0` and `H_t` has finitely many but at least one non-real zero for `0 < t < Λ`. Lesson: no argument stable under the heat flow at small positive time proves AAL.

**Positive configurations.** Abstract positive configurations with a non-attained top have lag excursion sets of finite measure; exact-spline divisors with Riemann–von Mangoldt counts and bounded two-prime coupling exist; tempered lattice-plus-one-pair configurations have finite off-line support. Lesson: counts and densities do not decide attainment.

**Selberg zeta functions with exceptional eigenvalues** (classical). Finitely many real zeros in `(½, 1)`, Euler product over geodesics, functional equation, norms `e^ℓ`.

### 6.2 Positive annihilators of finite zero sets

- Nonnegative two-prime Dirichlet polynomials with constant coefficient 1 vanish on any finite set in `Re s < 1`, with prescribed multiplicities, and stay `ε`-close to `1` on `Re s ≥ 1`.
- Nonnegative polynomials in the normalized Hecke operators `T₂, T₃` with constant 1 annihilate any finite set of resonances; their constant-mode value exceeds `2`.
- **Their cost.** The nonconstant mass of a positive annihilator is log-convex in `σ` and at least `1` at a zero, so mass `≤ ε` on a line `σ_hi` right of the zero forces mass `≥ ε^{−(Re ρ − σ_lo)/(σ_hi − Re ρ)}` on every line `σ_lo` left of it, sharp for a monomial. At unit mass every cancelling phase is `−1`, the zero is simple and the real part of the derivative is at least `log 2`.

Lesson: positivity can remove a finite set of zeros, at a cost paid on the critical side.

### 6.3 Models that violate RH but satisfy AAL

**The bounded-count model.** Every odd integer once, every multiple of `8` four times: `−3 ≤ N(x) − x ≤ 0`, zeta `ζ(s)(1 − 2^{−s} + 4·2^{−3s})`, zeros at `Re s ≈ 0.80` along a full vertical progression. Finite modifications of Euler factors only add periodic columns of zeros.

**Symmetric shifts `ξ(s+a)ξ(s−a)`.** Functional equation, Euler product, zeros moved off the line; they satisfy AAL iff `ξ` does.

**The golden fake.** Returns exactly under transport and fails the count.

**Dirichlet polynomials, periodic data, absolutely convergent Dirichlet series.** Vertically recurrent, so their zeros in a strip are absent or infinite (zero–one law). AAL holds for every finite truncation of `ζ`; multiplying by a factor absolutely convergent at the abscissa preserves AAL. A finite top layer can only come from the infinite tail.

**Davenport–Heilbronn** (classical). `≫ T` zeros in every substrip of `(½, 1)`.

**Function fields.** Zeros periodic modulo `2πi/log q`, so AAL is automatic.

**The near-count model.** Odd primes plus labels of norm `3, 4`: `|N(x) − x| ≪ (log x)²`, exactly the zeros of `ζ` on `Re s > 0`.

### 6.4 What the models force on a proof

1. **The Dirichlet series over `ℕ` must enter** (`ξ_β`, relocation and `H_t` lack it).
2. **The functional equation must enter.** Positive Euler products — continuous, discrete, integer-norm, rational-prime with multiplicative linear counting — all carry finite top layers and none continues to `Re s = ½` with a functional equation. For a countable Beurling system, `L¹` functional-equation defect `≤ 1/6400` on the line forces exactly the rational primes, and any displacement costs an explicit positive defect.
3. **The infinite tail must enter.** Every finite truncation satisfies AAL; the zeros of `ζ` are the zeros of the Euler tail at every cut.
4. **Positivity cannot do it alone**, but it constrains: positive annihilators exist at a left-growth cost, and rational surgery on `ζ` fails positivity at the first integer gap.
5. **The line itself cannot be used** beyond the functional-equation involution (shift invariance).

---

## 7. Approaches that fail, and why

**Hecke positivity.** Commutative Hecke `C*`-squares on truncated resonant Eisenstein states are Poisson-positive on the whole half-plane `Re u < 0`; positive Hecke polynomials annihilate finite resonance sets. They see nothing.

**Positivity of coefficients.** Positive two-prime polynomials annihilate any finite set; positive Euler products with integer or rational-prime norms carry finite top layers.

**Landau's theorem with a floor.** Making the top wave nonnegative by adding `Ce^{αu}` creates a real pole that shields the top zeros; squaring creates a real pole at `2β`.

**Exact identities.** Exact linear ledgers and cut identities are holomorphic at every zero; exact nonlinear identities (Selberg's `ζ(A² − A′) = ζ″`) hold for every analytic function; Chebyshev's identity sees a top zero only through `x^ρζ(ρ) = 0`.

**Diagonal decay; positivity of `Λ` in the jets; quantitative phase recurrence for the jets.** Nonzero moments with vanishing diagonal at `s = 2`; absolute values restore the radius `σ − 1`; the horizontal gain is strictly below `β − β₁ < ½`, sharply.

**Strong recurrence and typical heights.** Self-returns about a zero have density zero; `ζ` returns at positive density to its zero-erased cofactor; targets with a zero are approached only at tail-bad heights; every density-one statement misses the finite top.

**Recurrence of the primes.** At a zero a positive proportion of prime returns are not returns of `ζ`; limits of translates on `Re s > 1` fill the torus, twin included.

**Slow returns on discs crossing the line.** There `sup|ζ(s + iτ)| ≥ cτ^b` and aligned lengths are polylogarithmic, so the hypothesis is RH.

**The random Euler model.** Almost surely zero-free on `Re s > ½`.

**Repulsion.** Deuring–Heilbronn technology isolates exceptional zeros and argues towards ¬AAL; failures of AAL are of Siegel type.

**Extremal position.** The maximal-angle inequality has the polynomial model `w² − 2w + 2`.

**Count distance.** The near-count model has `ζ`'s zeros; the bounded-count model keeps AAL; the integer-norm one-off has linear counting.

**Mean spectra.** Rational relocation preserves every Cesàro square mean and Fourier mean in the strip.

**Self-improvement of a strip.** `Θ < 1 ⇒ Θ = ½` fails for shifted products.

**Finite-rank self-improvement transferred naively.** On curves a constant-factor bound at every level self-improves because the rank is finite; over `ℤ` `|ψ(x) − x| ≤ C√x` is false and tensor indices are `0` or `∞`, so there is no crude regime to start from.

**Weak analytic and sieve tools.** Gallagher converts but does not prove; Bohr's prime inequality needs uniform boundedness on a strip; prime-pair upper sieves bound unsigned counts; integer shifts lack a centred cancellation estimate; bilinear splitting adds no oscillation; functional-equation defect rigidity needs a positive Beurling spectrum for the deflated zeta, which does not exist.

**Thin samplings of the lag.** Telescoping quadrature produces measures with vanishing moments and arbitrarily small weights.

**Conclusion.** A proof must use the Euler product over `ℕ`, the infinite tail and the exact functional equation together, at an inequality, and must not use the position of the line.

---

## 8. The faces of the missing input

### 8.1 Tail and transport

**The problem (B89).** At each right zero, aligned heights where `ζ` stays polynomially bounded on a disc right of the line; in tail form, the Euler tail cancels the head on a disc about the zero at every cut.

**What is known.** Aligned shifts of length `N` exist below `(7N)^N`, with `N` polylogarithmic in the height; three-circles interpolation near the zero; the head never vanishes on `Re s > 0` and is frozen below resolution `1/log y`; every return at a zero is tail-bad at every cut; below the Kronecker scale `y ≍ log T` the tail is Gaussian conditionally on the head, moment by moment, while `log max A + k log Z ≪ log T`; arithmetic mean values bound smooth × prime moments by the diagonal plus gcd-class collision counts. Past the Kronecker scale nothing distributional is known.

**Why it is hard.** Alignment forces `|E_N(s + iτ)| ≈ exp(Σ_{p≤N}p^{−σ₀})`; the tail must cancel that factor and reproduce a zero, which the random model gives probability zero; with `N` polylogarithmic this is a statement about the primes between the Kronecker scale and a power of the height — the dark range. The proved mean values bound tail events from above; a return needs one to exist.

### 8.2 The lag

**The problem.** For every `a > 0`, `Φ(L) ≤ M_a e^{aL}` outside a set of Abel density zero. In prime form, `x∫_x^∞(ψ(u) − u)u^{−2}du ≥ −M_a x^{½+a}` outside a density-zero set of log-scales.

**What is known.** RH ⇔ `Φ` bounded above ⇔ `Φ` bounded below; RH ⇔ ZAL with excursion sets of finite measure or upper density zero; an attained top forces excursions of positive upper density; positive configurations with a non-attained top have excursion sets of finite measure.

**Why it is hard.** A one-sided bound at power precision on scales of density one; over finite fields the one-base form is Stepanov's argument, which needs a Frobenius.

**The open question.** Is the lag hypothesis weaker than a zero-free strip: does a zero at `β` force `Φ > e^{(β−½−ε)L}` on a set of infinite measure only when the top is attained, or always?

### 8.3 Jets, long correlations and power sums

**The problem.** Show that the long-shift correlation of the normalized von Mangoldt jets at a rightmost zero does not converge to `m²` (section 4.3); this contradicts any attained top.

**What is known.** Moment and diagonal limits; decay of exponentially many short shifts and of proper prime powers; high jets recover the multiplicity; Turán's second main theorem, separation-free, and its application to all `ξ`-zeros with a finite head.

**Why it is hard.** The coefficient mass concentrates at `log n ≈ k/β`; the remaining shifts reach beyond a fixed power of `n`, a binary prime problem of Hardy–Littlewood type behind the parity barrier; any argument must fail at `s = 2` and must use the high-height zero-free region quantitatively. A Turán contradiction needs an upper bound for `ψ(x) − x` below `x^Θ` on a positive proportion of geometric windows — which is a lag-type bound (8.2).

### 8.4 Integers and carries

**The problem.** Show that `ψ = log lcm(1, …, ⌊x⌋)` cannot obey the two-prime dilation collapse; equivalently, decide whether `N(x) = ⌊x⌋` can coexist with a finite oscillation of the prime error.

**What is known.** The carry `⌊kx⌋ − k⌊x⌋` is never constant for `k ≥ 2`; bounded multiplicities admit no Frobenius; the exact identity `Σ_{k≤x}L(x/k) = ⌊√x⌋` pins the Liouville function; every exact ledger is blind at every zero.

**Constraints.** The dilation coefficients are real polynomials in `b^Θ` and `cos(ω log b)`, so integrality does not pass to the combination, only the support and sizes of the jumps; inexact information at precision `x^{Θ−η}` is needed.

### 8.5 Count distance and integer Beurling systems

**The problem (B98).** Between count distance `o(log n)` (rigid: only the rational primes) and linear counting (one-offs exist with integer norms), which count distance forbids a finite top layer among positive integer-norm systems?

**What is known.** Count error `o(log n)` forces the rational primes; every nonclassical positive integer-norm system has `|N(n) − n| ≥ c log n` infinitely often; adding generators never creates a zero right of the count exponent, only deletion can, with exchange exponent `≥ β`; integer systems with count `x + O(x^σ)` exist for every `σ > 0`; the near-count model has `O(log²)` count error and only `ζ`'s zeros; the integer-norm one-off has linear counting.

**What a construction must avoid.** Multiplication by a Dirichlet series absolutely convergent at the abscissa of the new zeros; continuous prime densities; rational relocation of `ζ`'s zeros (negative density at the first gap).

### 8.6 Recurrence and the inner field

**The problem.** Weak recurrence about right zeros. **What is known.** The zero–one law of recurrence; recurrence modulo the local zero divisor; either infinitely many right zeros or a vanishing inner field; RH ⇔ inner-field decay with weak recurrence about off-line zeros. AAL asks whether the orbit ever restores the zero at large height, which by the transport count is again the existence of zeros.

### 8.7 The functional equation

**The problem (B103, B84).** A statement in which the functional equation acts on a finite top layer and its mirror bottom layer `1 − Θ + iγ_j` and meets a constraint that a finite oscillation cannot satisfy.

**What is known.** Every countermodel lacks the functional equation on `Re s = ½`: discrete one-offs blow up at `s = ½`, continuous ones carry none, and in a countable system any displacement of primes or integers from the rational ones forces an explicit positive defect; defect `≤ 1/6400` forces the rational primes. The functional equation does not single out the line (shift invariance). On graph black holes the functional equation is a nondegenerate Born rule and does not force damping, even with first-level counts and integrality [proved; RH-side, not AAL-side].

**Candidate quantities.** Theta-type transforms whose two asymptotic ends the functional equation exchanges, combined with the finite oscillation; a quantitative defect bound turning a finite top layer into a positive defect; the reflected Nyman–Beurling Gram, whose cotangent sums obey reciprocity; the Turán windows of the top layer with the reflected bottom layer inside the same power sums.

**Open sub-questions.** Does a positive Euler product with linear counting that continues across `Re s = ½` with a functional equation satisfy AAL (B103)? What is the smallest functional-equation defect that carries a one-off (B84)?

### 8.8 The finite stratum

**The problem (B13).** FOL ⇒ RH; equivalently AAL at `σ = ½`.

**What is known.** The stratum is one object read six ways (2.3); `K_ζ` is Krein–Langer there, with the on-line zeros as its positive part and one hyperbolic pair per right zero; Lindelöf and a zero-free half-plane hold; a non-blind prime tower decides RH [K]; the Hodge index fails at an explicit level; the explicit formula is RH up to finitely many terms; positive annihilators remove the off-line set at a computable left-growth cost; Turán applies to a finite set against a square-root remainder. Every one-off countermodel lies in the stratum (finite nonzero index), so the functional equation must enter.

**Forms of the missing input.** An FE statement on the critical line violated by a constant deficit `N(T) − N₀(T) = 2k`; a zero-or-infinity law for the actual two-prime lattice kernel (the corpus proves such laws under escape, mixing or decay); positivity of the kernel on one non-blind prime tower, a one-dimensional Toeplitz problem with finite negative index; a comparison of the forced growth of an annihilator on `Re s = ½` with what Lindelöf and finite index allow; exclusion of the `2k` persistent non-real Jensen roots outside the real inner region `|Re z| ≤ √(d log d)/100`.

---

## 9. Open problems

1. **AAL.** `Θ∞ = Θ`, in any form of section 2.
2. **The finite stratum (B13).** FOL ⇒ RH; equivalently RH above some height ⇒ RH; equivalently `κ(K_ζ) ∈ {0, ∞}`. Strictly weaker than AAL; first rung: a single off-line quartet `{ρ, ρ̄, 1 − ρ, 1 − ρ̄}`, `ρ` simple.
3. **ZAL ⇒ RH**, equivalently ZAL ⇒ AAL. Strictly between the previous two; in that world the top is attained and `Θ∞ = ½`.
4. **The functional equation on a finite layer (B103, B84).** Whether continuation across the line with a functional equation forbids a finite top layer in the class of positive Euler products with linear counting, and the smallest defect carrying a one-off.
5. **Slow aligned returns (B89).** Exhibit or exclude, at a right zero, aligned returns with polynomial bounds on a disc right of the line, in a stated class of configurations.
6. **The tail law at the Kronecker scale (B96).** A conditional law of the Euler tail at one moment past `y ≍ log T`; its off-diagonal is a count of shifted smooth × prime products.
7. **The lag versus a strip.** Decide whether the lag hypothesis is weaker than a zero-free strip.
8. **Long-shift jet correlations.** At a rightmost zero, a limit other than `m²` using the high-height zero-free region.
9. **Integer-norm count threshold (B98).** The count distance that forbids a finite top layer among positive integer-norm systems.
10. **The carry contradiction.** Whether `⌊x⌋` can coexist with a finite oscillation of `ψ`.
11. **Stepanov over `ℤ`.** A one-sided bound for `Φ` along one geometric progression; there is no analogue over `ℤ` of `x ↦ x^q`.
12. **Zero-or-infinity law for `K_ζ`.** The arithmetic mixing property of the two-prime lattice kernel that forces its index to be `0` or `∞`.

**How the faces compare.**
- Transport and recurrence reformulate the problem: producing a return is producing a zero.
- The lag, the jets and the power sums carry content and aim at NAT; each needs an unconditional input at power precision.
- Count distance and carries test integrality directly; integer norms with linear counting are already defeated by a one-off, so integrality must be the exact `⌊x⌋`.
- The functional-equation face is the only one not refuted on a countermodel.
- The finite-stratum face is the one with the most proved structure.

---

## 10. What a proof cannot be, and what it must be

### A proof of AAL cannot
1. use only positivity of the primes, an Euler product and a smooth count (continuous one-offs);
2. use only discreteness of the primes with an Euler product (discrete one-offs);
3. use only integer norms, nonnegative coefficients, an Euler product and linear counting (integer-norm one-off), or rational-prime labels with multiplicative linear counting (rational-prime one-off);
4. use only the functional equation, order, reality and vertical asymptotics (`ξ_β`, relocation);
5. use only positivity of coefficients to remove zeros (positive two-prime and Hecke annihilators);
6. use the position of the line `½` beyond the functional-equation involution (shift invariance);
7. be stable under the heat flow at small positive time;
8. rest on exact identities, linear or nonlinear in `Λ`;
9. rest on diagonal decay of moments;
10. rest on typical-height or density-one information;
11. rest on large-height receivers alone, which read only `Θ∞`;
12. rest on unconditional estimates of `ψ`, the Mertens function or the Liouville sum;
13. rest on the random Euler model;
14. rest on repulsion technology;
15. rest on recurrence of the primes or on transport alone;
16. rest on size bounds on discs crossing `Re s = ½`;
17. rest on extremal-position inequalities alone;
18. rest on count distance alone or on mean spectra.

### A proof of AAL must
1. **Couple heights.** Carry information from finitely many zeros at bounded height to infinitely many heights (explicit formula, dilations, vertical recurrence, Dirichlet alignment, power sums).
2. **Use the Dirichlet series over `ℕ` and the exact functional equation together**, through a property that fails on every model of 6.1.
3. **Be an inequality, not an identity.** By contradiction it may use the whole of section 4.
4. **Be shift-invariant**, or say where it uses more than the involution.
5. **Say whether it proves NAT, B13 or exactly AAL.** An attainment argument must name the real point where the top is detected.
6. **Place its scales** against the Kronecker scale `log T`, the head resolution `1/log y`, the VK length and the diagonal range.

### Questions to put to a proposed argument
- Where does the property of `ζ` enter that fails for each model of 6.1?
- Is any step an exact identity?
- At what precision does the contradiction occur, and what unconditional fact supplies it?
- How does information at the height of the top layer reach large heights?
- Is the argument stable under the heat flow, and invariant under symmetric shifts?
- Does it confuse attained with non-attained tops, or the finite stratum with the general case?

---

## 11. Milestones

1. **The finite stratum (B13): FOL ⇒ RH.** The asymptotic abscissa law at the single abscissa `½`. Its negative world has Lindelöf, a zero-free half-plane, 100% critical zeros, a Krein–Langer kernel with finite index, bounded heat and Jensen counts, a deciding prime tower and an explicit formula exact up to finitely many terms. Proving it turns six receivers (finite index, lattice index, heat count, `N_d`, eventual RH, eventual Gaussian gap) into RH receivers.
2. **Its first rung: one off-line quartet.** Exclude a world with exactly one quartet `{ρ, ρ̄, 1 − ρ, 1 − ρ̄}`, `ρ` simple, by applying each proved receiver of the stratum and recording the constraint on `(β, γ)`.
3. **ZAL ⇒ RH.**
4. **AAL for a restricted class of top layers:** a single simple conjugate pair above an infinite lower set, or a gap `Θ − Θ₂` above a stated bound.
5. **The functional-equation test on fakes (B103):** continue a discrete or rational-prime one-off across `Re s = ½`, or prove that critical continuation with linear counting forbids a finite top layer.
6. **A slow aligned return at one right zero**, exhibited or excluded in a stated class.
7. **A conditional tail law at one moment past the Kronecker scale.**
8. **A decision whether the lag hypothesis is weaker than a strip.**
9. **A count-distance threshold** that forbids an integer-norm one-off.

---

## 12. The first steps on the milestone

1. Write the one-quartet world explicitly: `ψ(x) − x = −2Re(x^ρ/ρ + x^{1−ρ̄}/(1−ρ̄)) + E(x)` with `E` the critical-zero contribution, and apply the window, tower, heat, Jensen and annihilator receivers of the stratum.
2. Test the escape and mixing hypotheses of the corpus zero-or-infinity theorems on the actual kernel of `⟨2, 3⟩` in the finite stratum, using the Lindelöf bound available there.
3. For one quartet, compute the blind primes and the explicit negative direction on a non-blind tower; test it against the functional-equation mirror `1 − ρ̄`.
4. Compute the cheapest positive two-prime annihilator of one quartet (unit-mass boundary, simple zero, real derivative `≥ log 2`) and its forced growth on `Re s = ½`; compare with Lindelöf-size bounds.
5. Follow the two persistent non-real reversed Jensen roots of the one-quartet world relative to the saddle edge.

---

## 13. Where it lives in the corpus

| Topic | Lean modules (under `formal/GaloisForLFunctions/`) | Key declarations |
|---|---|---|
| Definition, split, weak recurrence | `RHTower/ZetaWeakRecurrenceLadderCollapse` | `AsymptoticAbscissaLaw`, `riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw`, `riemannHypothesis_iff_zerosApproachLine_and_zeroDiscWeaklyRecurrent` |
| Eventual-to-global, shift invariance | `ZeroConfigurationGeometry/SymmetricShiftsPreserveTheAsymptoticAbscissaLaw` | `asymptoticAbscissaLaw_iff_xi_eventualToGlobal`, `asymptoticAbscissaLaw_iff_symmetricShift_eventualToGlobal`, `half_le_of_xi_eventualBound` |
| `Θ∞`, spectral gap, annihilator, twisted FE | `ZeroConfigurationGeometry/AsymptoticAbscissaSpectralGapAndTopAnnihilator` | `zetaAsymptoticAbscissa`, `not_asymptoticAbscissaLaw_iff_bilateral_spectralGap` |
| Finite oscillation and rigidity | `ZeroConfigurationGeometry/{TheOneOffsAreFiniteOscillationsOfThePrimeError, PrimeErrorFiniteOscillationRigidityAndSignChanges}` | `not_asymptoticAbscissaLaw_iff_primeErrorIsFiniteOscillation` |
| Dilation annihilation | `ZeroConfigurationGeometry/MultiplicativeDilationAnnihilationOfPrimeError` | `not_asymptoticAbscissaLaw_iff_twoPrime_dilationAnnihilation` |
| Jets, correlations, zero-free region | `ZeroConfigurationGeometry/{FiniteExceptionalLayersForcePersistentLowJets, FiniteExceptionalLayersGiveHighZeroFreeJetBounds, HighDerivativesRecoverARightmostZero, VonMangoldtShortShiftCorrelationsVanish, TheHorizontalJetGainHasASharpGapCeiling}`; `ArithmeticCorrespondencePositivity/PrimePairsRetainThePrimePowerField` | `not_asymptoticAbscissaLaw_has_positive_limit_after_short_shifts` |
| Power sums | `HTGeometry/PowerSumTuranLowerBound`; `RHTower/JointAncestryShellPowerSumCriterion` | `exists_norm_powerSum_ge`, `exists_norm_tsum_pow_mul_ge` |
| Attainment producers | `RHTower/{AsymptoticAbscissaLawProducers, WeilLagFunctionFiniteMeasureExcursion, WeilLagFunctionDensityZeroExcursion, WeilLagProgressionZerosApproachLine, WeilLagAsymptoticAbscissa, JointAncestryTypicalAsymptoticAbscissa, PolarGroundEnergySubexponentialZerosApproachLine}`; `ArithmeticKreinLangerTheory/PrimeTowersAndConeCouplingProduceAsymptoticAbscissaLaw`; `SquareRootThreshold/AttainedDepthIsVisible` | `riemannHypothesis_tfae_of_asymptoticAbscissaLaw`, `attainedDepth_visible` |
| Transport | `ArithmeticAuxiliaryDynamics/{TheMissingInputOfTransport, TheTransportOfAZeroIsEffective, TheSlowReturnBoundLivesRightOfTheLine, TheTransportCountOfAZero}` | `asymptoticAbscissaLaw_of_slowReturns_right`, `asymptoticAbscissaLaw_of_infinite_zeros` |
| Tail of a return | `TailArithmeticOfThePrimeOrbit/{TheTailOfAReturnCarriesTheZero, TheRecurrenceDichotomyOfTheTail, TheHeadIsFrozenAtItsResolution, TheConditionalMomentsOfTheTail}` | `tail_recurrence_dichotomy` |
| Finite stratum | `HeckeKreinToeplitz/{TheFiniteIndexStratumOfZetaIsLindelofDeep, TheWeilKernelIsKreinLangerOnTheFiniteStratum}`; `ArithmeticKreinLangerTheory/FiniteSupportMakesAlmostEveryPrimeDecideZeta` [K]; `SquareRootThreshold/HodgeClassificationOfFiniteOffLineSets`; `ConjugateDiagonalGeometry/LogScaleHeckeDefect/FiniteStratumAndCorridorClassification`; `RHTower/GaussianCentralGapLargeHeightFiniteOffLine` | `zetaKernel_finiteIndex_tfae`, `riemannHypothesis_tfae_zetaKernel`, `lindelof_of_negIndex_zetaKernel_lt_top`, `isKreinLanger_zetaKernel_iff`, `riemannHypothesis_iff_zetaKernel_prime_posDef`, `finiteOffLine_not_hodgeIndex`, `eventualFilteredCentralGapBudget_iff_finiteOffLine` |
| Zero-or-infinity laws for related kernels | `AdelicKreinGeometry/{MixingKillsNegativeSquares, HeckeSupportedStatesHaveIndexZeroOrInfinity}`; `RenormalizedIntersectionTheory/TheKunnethInertiaLaw` | — |
| Recurrence, inner field | `ArithmeticInnerFunctionTheory/TheZeroOneLawOfRecurrence`; `RHTower/{ZetaRecurrenceAtEveryPointModuloItsZeros, ZetaStrongRecurrenceReceiver}` | `zero_free_or_infinite_of_recurrent` |
| One-off models | `ArithmeticPositiveDuality/{BeurlingOneOffZeroCountermodelsAndDefectTradeoff, ADiscreteBeurlingOneOff, TheIntegerNormOneOffHasLinearCounting, ARationalPrimeBeurlingOneOff, TheRationalPrimeOneOffHasMultiplicativeCounting, SmallIntegrableDefectsForceTheRationalPrimes}` | `exists_integer_norm_linear_count_one_off`, `exists_rational_prime_multiplicative_linear_count_one_off` |
| Relocation | `ArithmeticPositiveDuality/{SymmetricRationalZeroRelocationBohrObstruction, FiniteZeroRelocationPreservesTheMeanSpectrum, NormalizedQuartetRelocation, NormalizedRelocationHasASignedDensity, TheNormalizedRelocationDensityHasZeroMass, TheFirstIntegerGapDetectsRelocation}` | `exists_normalizedRelocation_first_gap_obstruction` |
| Positive annihilators | `ArithmeticPositiveDuality/{PositiveTwoPrimeAnnihilators, PositiveAnnihilatorAccuracyForcesLeftGrowth, TheUnitMassBoundaryOfPositiveAnnihilators}`; `ArithmeticCorrespondencePositivity/{PositiveHeckeAnnihilatorsOfFiniteResonances, PositiveHeckeCancellationAmplifiesTheConstantMode}` | `annihilator_accuracy_forces_left_growth` |
| Count models, cuts, extremal zero | `RigidArithmeticOfCuts/{ABoundedCountWithANewZero, TheExtremalLawHasAModel}`; `SumProductArithmeticOfTheLogarithm/{PositiveNearCountEuler, CountDistanceRigidity}` | — |
| Curve template | `CountingHolography/{TheCountLawOfATrueCurveAtEveryGenus, TheCountLawOfEveryHyperellipticCurve}` | `hyperelliptic_countLaw_every`, `riemannHypothesis_evenHyperelliptic` |

---

## 14. Classical background

- **Landau's theorem.** A Dirichlet integral of a nonnegative measure is singular at the real point of its abscissa: the mechanism of every attainment argument and every failed floor argument.
- **Ω-theorems.** `ψ(x) − x = Ω±(x^{Θ−ε})`, and `Ω±(x^Θ)` when the top is attained; Littlewood: `Ω±(√x log log log x)`.
- **Turán's power-sum method.** Lower bounds for `|Σ z_i^ν|` on windows of exponents, the classical tool for zero-density and zero-free-region results.
- **Bohr–Landau.** Zeros right of `½ + δ` have density zero among all zeros; density estimates cannot see a bounded finite set.
- **Value distribution and universality.** Bohr–Jessen, Borchsenius–Jessen, Voronin, Bagchi (strong recurrence ⇔ RH).
- **Zero-free regions.** de la Vallée Poussin; Vinogradov–Korobov.
- **Exceptional zeros.** Siegel zeros and the Deuring–Heilbronn phenomenon.
- **Selberg zeta functions.** Exceptional eigenvalues give finitely many real zeros in `(½, 1)`.
- **Davenport–Heilbronn and Voronin.** Abundant off-line zeros without an Euler product.
- **The heat flow.** Ki–Kim–Lee: finitely many non-real zeros of `H_t` for `t > 0`; Rodgers–Tao: `Λ ≥ 0`.
- **Numerical verification.** Platt–Trudgian: RH up to height `3·10¹²`.
- **Function fields.** Weil; Stepanov's elementary proof; Bombieri's extension to all curves.
