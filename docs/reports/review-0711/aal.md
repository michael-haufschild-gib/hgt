# The asymptotic abscissa law (AAL)

This report covers:
- what AAL says;
- what a proof or a disproof would have to establish;
- everything the corpus has proved around it;
- the models it must defeat, the approaches that fail and why;
- the open problems.

Statements called *proved* are theorems of the Lean corpus. *Classical* marks results from the literature that are not formalized here, and *heuristic* marks unproved expectations. Section 12 says where each result lives in Lean.

---

## 1. The problem

### 1.1 Notation

**Zeros and abscissae.**
- Zeros are the nontrivial zeros `ρ = β + iγ` of `ζ`, counted with multiplicity.
- `Θ = sup Re ρ` is the zero abscissa.
- `Θ∞ = inf{σ ≥ ½ : only finitely many zeros have Re ρ > σ}` is the asymptotic abscissa. Equivalently, `σ ≥ Θ∞` exactly when all zeros above some height have `Re ρ ≤ σ`, so `Θ∞` is the limit superior of `Re ρ` as `|γ| → ∞`.
- `Θ₂ = sup({½} ∪ {Re ρ : Re ρ < Θ})` is the second abscissa.
- Always `½ ≤ Θ∞ ≤ Θ ≤ 1`.

**Hypotheses.**
- **ZAL** (zeros approach the line): `Θ∞ = ½`, i.e. finitely many zeros beyond every positive depth.
- **qRH** (quasi-RH): `Θ < 1`.
- **FOL**: finitely many off-line zeros.

**Tops.**
- A *right zero* has `β > ½`; the *top layer* is the set of zeros with `β = Θ`.
- The top is *attained* if some zero has `Re ρ = Θ`.
- **NAT** (no attained top) says that no zero attains a maximal real part above `½`. Equivalently: RH holds, or the supremum `Θ` is not attained.

**Functions.**
- `ψ` is Chebyshev's function.
- `Φ(L) = Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))` is the Weil lag function, which is real.
- `E_y = Π_{p≤y}(1 − p^{−s})^{−1}` is the Euler head, `M_y = 1/E_y` and `ζM_y` is the Euler tail.

### 1.2 The statement

> **AAL.** `Θ∞ = Θ`.

Each of the following is equivalent:
1. For every `h ≥ 0`: if only finitely many zeros satisfy `Re ρ > ½ + h`, then none does. This is the formal definition.
2. For every `σ ≥ ½`, the set of zeros with `Re ρ > σ` is empty or infinite.
3. For every `σ < Θ`, infinitely many zeros satisfy `Re ρ > σ`.
4. For every right zero `ρ` and every `r > 0`, infinitely many zeros satisfy `Re w > Re ρ − r`.

AAL says nothing about the value of `Θ`. It allows `Θ = 1`, and it allows the top to be attained or not.

### 1.3 The negation

> **¬AAL.** Some `σ ≥ ½` has finitely many, and at least one, zeros with `Re ρ > σ`. Equivalently `Θ∞ < Θ`.

So `ζ` has a finite top layer of zeros, separated by a gap from all the others. The top is then attained by finitely many zeros. Its full structure is section 4.

### 1.4 What proving and disproving mean

**Proving AAL** means proving one of the forms in 1.2 or section 2 for the actual `ζ`. Proving the hypothesis of any implication in section 5 for `ζ` also counts. Assuming that hypothesis proves nothing: it is the open mathematics.

**Disproving AAL** means producing:
- abscissae `½ ≤ β₁ < β* < 1` and a height `T*`;
- a finite nonempty layer of zeros on `Re s = β*`;
- a proof that every zero above height `T*` lies in `1 − β₁ ≤ Re s ≤ β₁`.

The last item is a zero-free region of quasi-RH type at all large heights. A disproof therefore refutes RH and proves quasi-RH at once. It cannot be a computation: a verified off-line zero refutes RH, but refutes AAL only once all zeros above it are confined, at every height, strictly to its left.

The expected answer is that AAL holds. Proving it is the realistic target.

### 1.5 Where AAL sits

| | ZAL (`Θ∞ = ½`) | not ZAL (`Θ∞ > ½`) |
|---|---|---|
| **AAL** | RH | RH fails; off-line zeros at unbounded heights with real parts accumulating at `Θ = Θ∞`; no finite top; `Θ = 1` not excluded |
| **not AAL** | finitely many zeros beyond each positive depth and a finite top at `Θ < 1`; includes the case of finitely many off-line zeros | a finite top layer above an infinite population accumulating at `Θ∞ ∈ (½, Θ)` |

Proved relations:
- **RH ⇔ ZAL ∧ AAL.** The proof is short. ZAL makes the zeros right of `½ + h` finitely many, and AAL then makes them absent.
- **RH ⇒ AAL**, trivially.
- **¬AAL ⇒ qRH ∧ ¬RH.** The finite top layer sits at `β* < 1` with nothing to its right. Hence **qRH or AAL** always holds.
- **ZAL ⇒ qRH.**
- **Under ZAL, ¬RH forces an attained top.** So under ZAL the statements AAL, NAT and RH coincide.

AAL implies no zero-free region. Zero configurations with `Θ = Θ∞ = 1` satisfy it.

AAL is therefore strictly below RH and is not RH-equivalent. It is independent of quasi-RH in the known sense: neither is known to imply the other. Together with ZAL it gives RH. It is false on several fake zeta functions (section 6), and its negation is one rigid object (section 4).

### 1.6 Points that are easy to get wrong

1. **¬AAL does not mean finitely many off-line zeros.** Below `β₁` there may be infinitely many. Finitely many off-line zeros, with at least one, is the special case where the off-line zeros are exactly the finite layers.
2. **AAL does not mean infinitely many off-line zeros.** Under RH it holds with none. AAL together with ¬RH does force infinitely many.
3. **AAL is weaker than NAT.** AAL permits a top `Θ > ½` attained by one zero, provided infinitely many zeros have real parts in every interval `(Θ − ε, Θ]`.
4. **The zero of maximal angle is not a sign of ¬AAL.** Write `Q(z²) = Ξ(z)`. Then `Q` has a zero of maximal argument whenever RH fails, in every world.
5. **A top layer is high.** No off-line zero has ordinate in `(0, 67]` (proved). Classically, RH is verified up to height `3·10¹²`.

---

## 2. Equivalent forms

AAL is equivalent to each of the following:

1. **`Θ∞ = Θ`.**
2. **No isolated spectral gap.** There are no `½ ≤ β₁ < β* < 1` and `T* > 0` such that all of the following hold:
   - `ζ` has no zero right of `β*`;
   - a finite nonempty conjugate-symmetric layer lies on `Re s = β*` below height `T*`, with its reflection on `Re s = 1 − β*`;
   - the strips `(β₁, β*)` and `(1 − β*, 1 − β₁)` are zero-free at all heights;
   - every other zero lies in `[1 − β₁, β₁]`.
3. **The prime error is not a finite oscillation.** There are no `β > ½`, `η > 0` and nonzero finite real trigonometric polynomial `T(u) = Re Σ_{ω∈S} c(ω)e^{iωu}` with

   `ψ(x) − x = x^β T(log x) + O(x^{β−η})`.
4. **No two-prime dilation annihilation.** For any two distinct primes `p ≠ q`, there are no finite frequency set `S`, `β ∈ (½, 1)` and `η > 0`, with a zero right of `β − η`, such that both dilation combinations
   - `Σ_k P_k ψ(x/p^k)` and
   - `Σ_k P_k ψ(x/q^k)`, where `P = Π_{ω∈S}(1 − 2b^β cos(ω log b)X + b^{2β}X²)` at `b = p` and at `b = q`,

   reduce `ψ` to its linear main term up to `O(x^{β−η})`. The proof uses the irrationality of `log q/log p`. One dilation base confines the zeros to vertical lattices; two incommensurable bases make the layer finite.
5. **Every right zero has infinitely many companions.** For every right zero `ρ` and every `r > 0`, infinitely many zeros satisfy `Re w > Re ρ − r`. This is the transport form.
6. **Finite subtraction never lowers the lag exponent.** Remove the waves of finitely many zeros from `Φ`. The resulting growth exponent is `Θ∞ − ½`. Without subtraction it is `Θ − ½`, by Landau's theorem. AAL says that subtracting finitely many waves never helps.

---

## 3. What a proof of AAL would give

**Statements that collapse to RH.** Under AAL each of the following is equivalent to RH (proved):
- ZAL;
- finitely many off-line zeros;
- finite Krein–Langer index of the Weil kernel `K_ζ`;
- bounded de Bruijn–Newman nonreal zero counts;
- finite critical source energy;
- eventual Hadamard positivity;
- an eventual Gaussian central-gap budget;
- a finite-dimensional odd bound-state space.

**Large-height gauges.** Every large-height gauge reads the global abscissa:
- eventual Hadamard positivity right of `½ + h` holds exactly when all zeros satisfy `Re ρ ≤ ½ + h`;
- the eventual central-gap rate equals the all-height rate;
- both are equivalent to the global cubic-spline prime-sum bound.

**Effect across the corpus.**
- Every programme whose large-height receiver delivers "all but finitely many" becomes an RH programme. This covers finite index, bounded heat counts, finite support and eventual sign statements.
- Proving RH reduces to proving ZAL.
- The one-off countermodels stop being models of `ζ`.

**What AAL does not give.** No zero-free region and no ZAL. The remaining half, ZAL, is at least quasi-RH.

---

## 4. The world without AAL

Everything in this section is proved, and a proof by contradiction may use all of it.

### 4.1 The zero configuration

**The spectral gap.**
- There are `½ ≤ β₁ < β* = Θ < 1` and `T*`.
- A finite conjugate-symmetric top layer lies on `Re s = Θ` below `T*`, and its reflection lies on `Re s = 1 − Θ`.
- The strips `(β₁, Θ)` and `(1 − Θ, 1 − β₁)` are zero-free at all heights.
- Every zero above `T*`, and every zero outside the two layers, lies in `[1 − β₁, β₁]`.

Also `Θ∞ ≤ Θ₂ < Θ`.

**The high zero-free region.**
- `ζ` is zero-free on `Re s > β₁, |Im s| > T*`.
- On discs at distance `δ` from the zeros, the logarithmic derivative obeys jet bounds `|(ζ′/ζ)^{(k)}| ≤ k! C log(t + r)/(δ r^k)`.
- Derivative returns to the top layer can only occur at exponentially large heights.
- Classically, the high zero-free region gives Lindelöf-type bounds `|ζ(σ + it)| = t^{o(1)}` for `σ > β₁`.

### 4.2 The prime error

**The finite oscillation.**

`ψ(x) − x = x^Θ T(log x) + O(x^{Θ−η})` for every `0 < η < Θ − Θ₂`.

**Rigidity of the witness.** Every such expansion has:
- exponent exactly `Θ`;
- frequencies exactly the ordinates `μ` of the top layer;
- coefficients exactly `−ord_{Θ+iμ}(ζ)/(Θ + iμ)`;
- zero constant mode;
- a unique profile `T`.

No saving `η` larger than `Θ − Θ₂` is possible. Unconditionally, no finite oscillation approximates `ψ(x) − x` to `O(x^{σ₀})` with `σ₀ < ½`: the reflected zeros would then be confined to bounded height.

**Sign changes.** There are `L, δ > 0` such that every logarithmic window `[u, u + L]` far out contains points where `ψ(e^u) − e^u > δe^{Θu}` and points where it is `< −δe^{Θu}`.

**Parity transfer.** `Σ_{n≤x}(−1)^nΛ(n) = 2⌊log₂⌊x⌋⌋ log 2 − ψ(x)` exactly, so the oscillation transfers to the alternating sum.

**Dilation annihilation.**
- At every base `b > 1`, the dilation combination `Σ_k P_k ψ(x/b^k)` annihilates `x^Θ T(log x)` identically.
- It multiplies `x` by `κ_b ≥ (1 − b^{Θ−1})^{2|S|} > 0`, leaving `κ_b x + O(x^{Θ−η})`.
- One base confines every zero right of the error exponent to `Re ρ = Θ` and to the lattices `α + (2π/log b)ℤ`.
- Two prime bases make the layer finite.

**The top annihilator.** `D(s) = Π_{ρ∈F}(1 − b^{ρ−s})^{m(ρ)}` vanishes on the top layer `F` and is bounded away from zero on `Re s ≤ ½`.

**The twisted functional equation.** Dividing `ξ` by the finite Blaschke product of the top layer twists `s ↔ 1 − s` by a nonconstant unimodular phase `B(s)²`.

### 4.3 Jets at a rightmost zero

Let `ρ` be a top zero of multiplicity `m` and put `a_{k,n} = Λ(n)(log n)^k/(k! n^{ρ+1})`. Then:
- `Σ_n a_{k,n} → −m`. At the unit shift the pole correction vanishes because `|γ| ≥ 4`.
- The diagonal tends to zero: `Σ_n |a_{k,n}|² → 0`.
- So the whole squared mass sits off the diagonal: `Re Σ_{n≠j} a_{k,n}\overline{a_{k,j}} → m²`.
- The limit `m²` survives removing all shifts `h ≤ r^k` in both orientations, for `1 < R < Re ρ + ½` and `r < R²`. It also survives removing every proper prime power.

So the obstruction lives in a long-shift correlation of the primes. It cannot be on the diagonal or among short shifts.

A calibration limits this. At the real centre `s = 2` the same arithmetic sequence has moments tending to `+1` while its diagonal tends to zero, so diagonal decay alone can never exclude a nonzero moment.

The jet argument uses only that the rightmost zero is attained.

### 4.4 Transport, returns and lags

**Returns of `ζ` near a top zero.**
- **Bounded translates never reach the top layer.** Every phase return (shifts `τ_j` with `n^{−iτ_j} → 1` for all `n`) has unbounded translates on every connected domain joining a top zero to `Re s > 1`.
- **Polynomial bounds fail at aligned shifts.** At every aligned shift past some height, `|ζ|` exceeds every polynomial in the aligned length somewhere on the disc about each top zero.
- **Returns are rare in every world.** Returns of `ζ` to itself on a disc about any right zero are tail-bad at every cut and have density zero.
- **Under ¬AAL they have finite total measure.** Returns strong enough to move a zero are bounded in measure by the number of zeros they can move to, and here those zeros are finitely many.

**Lags.**
- For `a < Θ − ½` and every `M`, the set `{L : Φ(L) > Me^{aL}}` has upper density at least `Re(1/(ρ₀(1−ρ₀)))/(4Σ_ρ|1/(ρ(1−ρ))|)`.
- Every lag progression `m ↦ Φ(mℓ)`, `ℓ ≠ 0`, is unbounded above.

**Spectral readings of the attained top.**
- The restricted Weil ground energy decays like `μ₀(B) ≤ −c e^{2(Θ−½)B}/B³`.
- `K_ζ` is bounded on only finitely many prime towers.

### 4.5 The special case of finitely many off-line zeros

If the off-line zeros are finitely many and nonempty:
- `K_ζ` has finite index, which forces Lindelöf and quasi-RH;
- the inner field tends to zero on every vertical line right of `½`.

### 4.6 What the world without AAL does not provide

- **Finiteness of the off-line zeros** in general.
- **Simple zeros**, or **ℚ-linear independence of the top ordinates**.
- **Any information about a possible second finite layer** between `Θ∞` and `Θ`.

### 4.7 The precision of this world

**The unconditional limit.** Unconditionally, `ψ(x) − x ≪ x exp(−c(log x)^{3/5}(log log x)^{−1/5})` (Vinogradov–Korobov).

**The precision of this world.** Without AAL, the prime error is a finite oscillation at size `x^Θ`, `Θ < 1`, with a power-saving remainder. No unconditional estimate of `ψ`, of the Mertens function or of the Liouville sum resolves the scale `x^Θ`. So no such estimate distinguishes AAL from its failure.

**Where a contradiction can come from.** Exactly three sources:
1. **Information valid at every precision.** Exact identities are blind (section 7). What remains is positivity, integrality and discreteness: exact counts, carries, jumps and unique factorization.
2. **Unconditional power-saving inequalities for other objects.** Mean value theorems for Dirichlet polynomials, the large sieve, Weil's bounds.
3. **The regularity this world forces at large heights.** The zero-free region and Lindelöf-type bounds right of `β₁`, played against the zero at low height.

---

## 5. What is known to imply AAL

Each implication below is proved. Each hypothesis is open for `ζ`.

### 5.1 Attainment: implications that prove NAT

**The common mechanism.** An attained top `ρ₀` carries a weight with positive real part, `Re 1/(ρ₀(1−ρ₀)) > 0`. Dirichlet's theorem aligns the finitely many top phases, and a twist `1 + cos(γ₀L)` moves the weight to a real exponent. A one-round Landau theorem then detects that exponent.

A non-attained supremum has no such real point. That is the only escape, which is why these arguments prove NAT rather than RH.

| Hypothesis | Comment |
|---|---|
| `Φ(m log b)` bounded above along one geometric progression `b^m` | over a finite field this is Stepanov's argument along `qⁿ` |
| `Φ(mℓ)` bounded above along one arithmetic progression, any `ℓ ≠ 0` | RH ⇔ ZAL ∧ one bounded progression; RH ⇔ the set of good spacings is not meagre |
| integer lags bounded above on a logarithmically dense set of integers | sampling sets with power-saving gaps `O(n^{1−δ})` are RH-complete; log-dense meshes with sub-power gaps give only AAL |
| for every `a > 0`, `Φ(L) ≤ M_a e^{aL}` outside a set of finite measure, of Abel density zero, or of lower density zero | the lag form, section 8.2 |
| subexponential lower bounds for the two-bump prime-window functional along one grid `kℓ` | the same bound at all real `v` is equivalent to RH |
| nonnegative twisted plateau Weil energies | — |
| joint-ancestry (JAS) positivity in several forms: real-amplitude at level one; dressed at a level `σ ≤ 1`; typical positivity at every level in `(½, 1)`; constant-vector positivity on infinitely many dyadic prime shells `(N, 2N]` | — |
| `K_ζ` bounded, or positive definite, on infinitely many prime towers | — |
| bounded coupling of `K_ζ` on one positive two-prime cone `⟨p⟩₊ × ⟨q⟩₊` | this bound cannot select a zero width (exact-spline models with a bounded cone exist), but it still implies AAL |
| a subexponential lower floor for the restricted Weil ground energy | — |
| eventual nonnegativity of single-scale grid factorial-tent energies | — |
| every off-line zero is strictly exceeded in distance from the line by another | this is a form of NAT itself |

### 5.2 Transport: implications that prove exactly AAL

**The common mechanism.** Phase returns `n^{−iτ_j} → 1` always exist, by Kronecker's theorem, and translates of `ζ` along them converge to `ζ` on `Re s > 1`. A bound on the translates near a zero gives convergence near it, by Vitali's theorem or by three circles. Rouché's theorem then copies the zero to the translated height.

| Hypothesis | Comment |
|---|---|
| weak recurrence: return shifts beyond every height for every disc in the right strip, or only for discs about right zeros | RH ⇔ ZAL ∧ weak recurrence about off-line zeros. Bagchi's strong recurrence (positive density) implies weak recurrence and is equivalent to RH |
| every right zero has infinitely many zeros with real part above `Re ρ − r`, for every `r > 0` | this is AAL itself (form 5) |
| a phase return with bounded translates on a connected domain joining each right zero to `Re s > 1` | every such domain lies in `Re s > ½` |
| **slow aligned returns right of the line** (B89): for each right zero `ρ = β + iγ` there are `σ₀ ∈ [½, β)` and shifts `τ` at which `n^{−iτ}` is within `1/N` of `1` for all `n < N`, of arbitrarily large `N` and `τ`, with `|ζ(s + iτ)| ≤ N^A` on the disc about `3 + iγ` with left edge `σ₀` | `A` is an explicit transport exponent depending on `β` and the radius. On discs that cross `Re s = ½` the same hypothesis is equivalent to RH, because `|ζ|` is at least a power of the height there |
| decay of the inner field on every vertical line, together with weak recurrence about off-line zeros | this is equivalent to RH |

**Transport is a reformulation, not a free input.** The returns of strength `m/2` on an isolating disc of radius `r` have measure at most `2r` times the number of zeros in the translated strip. Returns strong enough to move a zero are as rare as the zeros they move. Every transport hypothesis therefore asks to produce zeros at large heights.

### 5.3 Thin, thick and compressing receivers

**Thick receivers.** A receiver decides RH outright when its test family is thick: an interval or non-meagre set of lag spacings, all heights, or all prime sets in dyadic windows.

**Compressing receivers.** A receiver also decides RH when its coordinate compresses height, so that every top is attained (Li or Cayley coordinates, or the multiplier `z/log(2 − z²)`). Compression has a resolution cost: to see a zero of depth `δ` at height `γ` one needs primes up to `γ^{(2/δ)w_max/w(γ)}` instead of `γ^{2/δ}`.

**Thin receivers.** A thin family in a height-uniform coordinate sees only attained tops. It is worth exactly NAT, and needs a separate ZAL producer to reach RH.

AAL is the attainment gap of a coordinate, not of the zeros.

---

## 6. Models

### 6.1 Models that violate AAL

**Continuous Beurling one-offs.** For `1/3 < μ < 1/2`, `0 < ν < 3μ − 1`, `γ ≠ 0` there is a continuous Beurling system with:
- positive prime and integer densities and an Euler product;
- integer count `N(x) = ρx + C + o(1)`, better than `ℤ`'s;
- `ζ_B(σ + it) → 1` on every vertical line;
- zeros right of `½` exactly `(1 − μ) ± iγ`.

It has no zeros at large height at all, so it satisfies ZAL and violates AAL. Weak recurrence fails for it. Lesson: positivity, an Euler product and an excellent count do not give AAL.

**A discrete Beurling one-off** (being formalized).
- The primes are `p_k = e^{t_k}`, with `#{k : t_k ≤ x}` within one of the continuous density.
- The Euler product equals the continuous zeta times `e^{sΛ(s)+R(s)}`, with `Λ` holomorphic on `Re s > 0` and `R` on `Re s > ½`.
- The zeros right of `½` are the same pair.
- The continuation blows up at `s = ½`, because `Σ 1/p_k = ∞`. To reach the line, a discrete one-off would need Riemann's correction `−½W(x/2)` in its prime count.

Lesson: discreteness of the primes does not give AAL either. Classically, Broucke, Debruyne and Vindas also built discrete Beurling systems with one-off zeros.

**`ξ_β = (s − β)(s − 1 + β)ξ`.** It has the functional equation, order one, reality and the Gamma factor, and a real off-line pair implanted. It is not a Dirichlet series and has no Euler product. Lesson: functional equation, order and reality do not give AAL.

**Symmetric rational zero relocation.**
- It keeps the functional equation, reality on the critical line and the `1 + O(1/|t|)` vertical asymptotics.
- It implants an off-line zero.
- In exchange it destroys Bohr almost periodicity, and every Dirichlet-series representation, on every line `Re s > 1`.

Lesson: a proof must use the Dirichlet series on `Re s > 1`.

**Heat deformations.**
- `H_t` has no nonreal zeros of small imaginary part at large height for `t > 0` (Ki–Kim–Lee).
- If RH fails, then `Λ > 0`, and for `0 < t < Λ` the function `H_t` has finitely many but at least one nonreal zero.
- So if RH fails, the heat family violates AAL on all of `(0, Λ)`. It does so arbitrarily close to `Ξ`.

Lesson: no argument stable under the heat flow at small positive time can prove AAL.

**Positive configurations.**
- Abstract positive zero configurations with a non-attained top have lag excursion sets of finite measure.
- Exact-spline model divisors with Riemann–von Mangoldt counts and bounded two-prime coupling exist.

Lesson: counts and densities do not decide attainment.

**Selberg zeta functions with exceptional eigenvalues** (classical). An eigenvalue `λ < ¼` gives a real zero in `(½, 1)`. There are finitely many such, while the remaining nontrivial zeros of a cocompact group lie on the line. Selberg zetas have an Euler product over geodesics, a functional equation and a prime geodesic theorem, but norms `e^{ℓ}` rather than integers. The natural finite top layers are spectral and real.

### 6.2 Models that violate RH but satisfy AAL

**The bounded-count model.**
- Count every odd integer once and every multiple of `8` four times.
- The counting function is nonnegative, integral, multiplicative and satisfies `−3 ≤ N(x) − x ≤ 0`.
- Its zeta is `ζ(s)(1 − 2^{−s} + 4·2^{−3s})`, with zeros at `Re s ≈ 0.80` along a full vertical progression.

It violates ZAL, not AAL. Finite modifications of Euler factors only add periodic columns of zeros.

**The golden fake.** It returns exactly under transport and fails the count. Transport is free on fakes.

**Dirichlet polynomials and periodic data.** These are vertically recurrent. For any vertically recurrent entire function, the zeros in a strip are either absent or infinite (the zero–one law of recurrence). Zeros of Dirichlet polynomials recur in every window, effectively. So AAL holds for every finite truncation of `ζ`, and any failure must come from the infinite tail.

**Absolutely convergent Dirichlet series.**
- Such a series is Bohr almost periodic on its half-plane of absolute convergence, hence vertically recurrent, hence subject to the zero–one law.
- Multiplying a function satisfying AAL by such a factor preserves AAL there.
- So a finite top layer can only be created by a factor that is not absolutely convergent at its abscissa.

**Davenport–Heilbronn** (classical). Linear combinations of Dirichlet `L`-functions with a functional equation and no Euler product have `≫ T` zeros in every substrip of `(½, 1)`. Their off-line zeros are generic and abundant.

**Function fields.** Zeros are periodic modulo `2πi/log q`, so AAL is automatic. Over `𝔽_q`, RH is ZAL, which is free because the spectrum is finite, plus one bounded progression, which is Stepanov's argument along `qⁿ`.

**The near-count model.**
- Take the odd primes together with extra labels of norm `3` and `4`.
- The generators are positive and the norms are integers, with `|N(x) − x| ≪ (log x)²`.
- Its zeta is `ζ(s)/((1 + 2^{−s})(1 − 3^{−s}))`, with exactly the zeros of `ζ` on `Re s > 0`.

Count distance alone does not measure the insertion of right zeros.

### 6.3 What the models force on a proof

1. **The Dirichlet series over `ℕ` must enter.** `ξ_β`, relocation and `H_t` violate AAL and lack it.
2. **Integer norms, or the exact functional equation in its Beurling-rigid form, must enter.** Positive Euler products alone are violated by the Beurling one-offs. The functional equation separates them: for a countable Beurling system, a vanishing `L¹` defect of the functional equation on the critical line forces exactly the rational primes, and a prime mismatch at `N` costs defect `> 1/(400N²)`.
3. **The infinite tail must enter.** Every finite truncation satisfies AAL. The zeros of `ζ` are the zeros of the Euler tail `ζM_y` at every cut `y`.
4. **The decisive test case is open.** No system with integer norms and nonnegative generators is known to violate AAL. Whether one exists is open.

---

## 7. Approaches that fail, and why

**Hecke positivity.** Commutative Hecke `C*`-squares on truncated resonant Eisenstein states are Poisson-positive on the whole half-plane `Re u < 0`, on and off the line. They see nothing.

**Landau's theorem with a floor.** Making the top wave nonnegative by adding `Ce^{αu}` creates a real pole that shields the top zeros. Squaring the wave creates a real pole at `2β` with positive residue.

**Exact identities.**
- Exact linear ledgers and cut identities are holomorphic at every zero, because `ζ(ρ) = 0` cancels the top terms: the zeros are exactly the power-law kernel of the cut system.
- Exact nonlinear identities are blind as well. Selberg's `ζ(A² − A′) = ζ″` holds for every analytic function in the form `f(A² − A′) = f″`.
- Chebyshev's identity `Σ_{n≤x}Λ(n)⌊x/n⌋ = log⌊x⌋!` sees a top zero only through `x^ρζ(ρ) = 0`.

**Diagonal decay.** At the real centre `s = 2` the moments are nonzero while the diagonal vanishes (section 4.3).

**Positivity of `Λ` in the jets.** Absolute values restore the real-axis radius `σ − 1`, which is smaller than the detection radius `σ − β`.

**Quantitative phase recurrence for the jets.** The horizontal gain available is strictly below `β − β₁ < ½`, and this ceiling is sharp. It is a bound on parameters, not on return times.

**Strong recurrence.**
- Strong recurrence at a point holds exactly when `ζ` does not vanish there.
- Self-returns about a zero have density zero.
- Around any point, `ζ` returns at positive density to the cofactor with the local zeros erased. The orbit erases the zero rather than restoring it.

**Typical heights.**
- Targets that are nonvanishing on the disc are approached at positive density.
- Targets with a zero are approached only at heights that are tail-bad at every cut, and those heights have density zero.
- Every density-one statement misses the finite top.

**Recurrence of the primes.** The primes of any finite family return at positive density. At a zero, however, a positive proportion of prime returns are not returns of `ζ`. The limits of translates on `Re s > 1` fill the whole torus, including the twin `ζ(2s)/ζ(s)`, so recurrence cannot see parity.

**Slow returns on discs crossing the line.** On every disc of radius `R > 5/2` about `3 + iγ`, `sup |ζ(s + iτ)| ≥ cτ^b`. Aligned shifts of length `N` have `N < 1024(log τ)⁴(log log τ)²`. So polynomial bounds in `N` fail there, and on such discs the slow-return hypothesis is equivalent to RH.

**The random Euler model.** It is almost surely zero-free on `Re s > ½`. So it assigns probability zero to every return that copies a zero.

**Almost periodicity of `ζ` in the strip.** Only Besicovitch almost periodicity holds there, and it does not localize zeros.

**Repulsion.** Deuring–Heilbronn and Landau–Page technology makes exceptional zeros isolated, so it argues towards ¬AAL. Twisting maps a complex isolated top `β + iγ` to a real double zero `β` of the positive family `ζ²(s)ζ(s + iγ)ζ(s − iγ)`. Failures of AAL are of Siegel type.

**Extremal position.**
- At the zero of maximal angle every Hadamard factor points the same way.
- This gives a Hermite–Biehler inequality `|Q(t̄w₀)| < |Q(tw₀)|` for `Im t > 0`, and a Stieltjes sign.
- The real quadratic `w² − 2w + 2`, with zeros `1 ± i`, satisfies the whole inequality.

**Count distance.** The near-count model has `ζ`'s zeros, and the bounded-count model keeps AAL.

**Weak analytic and sieve tools.**
- *Short-interval variance (Gallagher):* converts a second-moment bound into a prime variance bound; it does not prove one.
- *Bohr's prime inequality:* needs uniform boundedness on a strip, which the `log t` bound does not supply.
- *Prime-pair upper sieves:* bound unsigned counts, not the signed normalized correlation.
- *Integer shifts `F(s) − F(s + 1)`:* replace exponential scales by polynomial ones, with prime kernel `(1 − 1/n)^k`, but a centred cancellation estimate is missing.
- *Multiplicative bilinear splitting:* adds no oscillatory interaction.
- *Functional-equation defect rigidity:* needs a positive Beurling spectrum for the deflated zeta, which does not exist.

**Thin samplings of the lag.** Telescoping circle quadrature produces discrete measures whose moments vanish while their weights are as small as wanted. Thin samplings are blind on the zero side.

**The conclusion of the direct attempts.** A proof must use the Euler product and the exact functional equation together. It must pass outside commutative Hecke expectations.

---

## 8. The faces of the missing input

### 8.1 Tail and transport

**The problem (B89).** At each right zero, find aligned heights where `ζ` stays polynomially bounded on a disc right of the line. In tail form: at such heights the Euler tail cancels the head on a disc about the zero, at every cut.

**What is known.**
- Aligned shifts of length `N` exist below height `(7N)^N`.
- At large height they have `N` polylogarithmic in `τ`.
- On `Re s ≥ 2` the translate is within `4/N` of `ζ`. Three circles give `|ζ(s + iτ) − ζ(s)| ≤ (4/N)^{1−t}(2M)^t` near the zero.
- The head never vanishes on `Re s > 0`.
- The head is frozen below its resolution: `|log|E_y(s + iv)| − log|E_y(s)|| ≤ 2|v|(log y + log 4)` on `Re s ≥ 1`.
- Every return at a zero is tail-bad at every cut, with a tolerance independent of the cut.
- Below the Kronecker scale `y ≍ log T` the tail is Gaussian conditionally on the head, moment by moment. This holds while the head length and moment order satisfy `log max A + k log Z ≪ log T`. Past that scale nothing is known.

**Why it is hard.**
- On the left part of the disc, alignment forces `|E_N(s + iτ)| ≈ |E_N(s)| ≈ exp(Σ_{p≤N}p^{−σ₀})`. Heuristically this is `exp(cN^{1−σ₀}/log N)`.
- So the tail must cancel the head by that factor, and in doing so it reproduces a zero. The random model gives this probability zero.
- With `N` polylogarithmic in the height, the cancellation is a statement about the primes between the Kronecker scale and a power of the height. This is the dark range.
- By the transport count, producing such returns is the same as producing zeros.

**Progress would be:**
- a slow return at one right zero, exhibited or excluded within a stated class of configurations;
- a conditional tail law at one moment past the Kronecker scale.

A first concrete step is to write the off-diagonal of the resonator mean `∫_T^{2T}|R|²|ζM_y|²` at resonator length `≍ T` as a sum over shifted smooth × prime products, and to compute what a finite oscillation contributes to it.

### 8.2 The lag

**The problem.** For every `a > 0`, show `Φ(L) ≤ M_a e^{aL}` for all `L ≥ 0` outside a set of Abel density zero.

**Prime form.** With `x = e^L`,

`Φ(log x) = −x^{−½}(x∫_x^∞(ψ(u) − u)u^{−2} du + log 2π) + O(x^{−5/2})`.

So the hypothesis is a one-sided lower bound for the tail-averaged prime error:

`x∫_x^∞(ψ(u) − u)u^{−2} du ≥ −M_a x^{½+a}` outside a density-zero set of log-scales.

**What is known.**
- Under RH, `Φ` is bounded above. RH is equivalent to `Φ` bounded above, and to `Φ` bounded below.
- RH is equivalent to ZAL together with excursion sets of finite measure, or of upper density zero.
- An attained top forces excursions of positive upper density.
- Positive configurations with a non-attained top have excursion sets of finite measure.

**Why it is hard.** It is a one-sided bound at power precision on scales of density one. No unconditional method gives one-sided power-precision prime bounds on any set of scales of positive density. Over finite fields the one-base form is Stepanov's argument, and it needs a Frobenius.

**The open question.** Is the lag hypothesis weaker than a zero-free strip for `ζ`? That is, does a zero at `β` force `Φ > e^{(β−½−ε)L}` on a set of infinite measure only when the top is attained, or always?

### 8.3 Jets and long correlations

**The problem.** Section 4.3 shows that the failure of AAL forces a specific long-shift correlation of the normalized von Mangoldt jets at a rightmost zero to converge to `m²`. A theorem showing that this correlation does not converge to `m²` would contradict the finite top, and indeed any attained top.

**What is known.**
- The moment and diagonal limits of section 4.3.
- The decay of exponentially many short shifts.
- The decay of proper prime powers.
- High jets recover the multiplicity of the rightmost zero of an entire function.
- Jets of finitely many poles decay far above their heights.
- Turán's second main theorem in separation-free form: some `ν ∈ [M + 1, M + N]` has `|Σ z_i^ν| ≥ 1/(2eN(6(N + 1)(M + 2N + 2))^N)`.

**Why it is hard.**
- The coefficient mass concentrates at `log n ≈ k/β`.
- The removed shifts reach `h ≈ n^{β log r}` with `β log r < 2β log(β + ½) < 1`, so what remains is a correlation at shifts beyond a fixed power of `n`.
- An asymptotic for such weighted correlations `Σ Λ(n)Λ(n + h)` is a binary prime problem of Hardy–Littlewood type, behind the parity barrier.
- Any argument must fail at the real centre `s = 2`.
- It must use the high-height zero-free region quantitatively. Qualitative recurrence does not relate the jet order `k` to the height.

### 8.4 Integers and carries

**The problem.** Show that `ψ = log lcm(1, …, ⌊x⌋)` cannot obey the two-prime dilation collapse. Equivalently, decide whether `N(x) = ⌊x⌋` can coexist with a finite oscillation of the prime error.

**What is known.**
- The carry `⌊kx⌋ − k⌊x⌋ = ⌊k{x}⌋` is never constant for `k ≥ 2`, and bounded multiplicities admit no Frobenius.
- The exact cut identity `Σ_{k≤x} L(x/k) = ⌊√x⌋` determines the Liouville function on every integer, so parity is not missing information: only the size of the Liouville sum `L` is.
- Every exact ledger is blind at every zero.

**Two constraints on this face.**
- **The coefficients are real.** The dilation coefficients are polynomials in `b^Θ` and `cos(ω log b)`, so integrality of `lcm` does not pass to the combination. What passes is the discrete support of the jumps, at `b^k q^a`, and their sizes `P_k log q`.
- **Inexact information is needed.** A carry argument must use information that is not an identity, such as the distribution of the fractional parts `{x/n}`, at precision `x^{Θ−η}`.

### 8.5 Count distance and integer Beurling systems

**The problem.** Does a Beurling system with integer norms and nonnegative generators exist whose zeta has a finite top layer right of its count exponent? What count distance does it need? If every such system with count error below a suitable threshold satisfies AAL, then AAL for `ζ` follows by taking `ℤ` itself.

**What is known.**
- A count error of `o(log n)` forces the rational primes.
- Every nonclassical positive integer-norm system has `|N(n) − n| ≥ c log n` infinitely often.
- Adding generators never creates a zero right of the count exponent. Only deleting them can, and with an exchange exponent at least `β`.
- Integer systems with count `x + O(x^σ)` exist for every `σ > 0`.
- The near-count and bounded-count models of 6.2.

**What a construction must avoid.**
- Multiplication by a Dirichlet series absolutely convergent at the abscissa of the new zeros, since such a factor keeps AAL.
- Continuous prime densities, since they lack integer norms.

### 8.6 Recurrence and the inner field

**The problem.** Weak recurrence about right zeros: cofinal return shifts on discs about each right zero.

**What is known.**
- The zero–one law of recurrence.
- Recurrence modulo the local zero divisor: `ζ` returns at positive density to the zero-erased cofactor, and the Dirichlet heads approximate it uniformly in the cutoff.
- Either `ζ` has infinitely many right zeros, or the inner field tends to zero on vertical lines.
- RH is equivalent to inner-field decay together with weak recurrence about off-line zeros.

AAL asks whether the orbit ever restores the zero at large height. By the transport count, that is again the existence of zeros.

---

## 9. Open problems

1. **AAL.** `Θ∞ = Θ`, in any of the forms of section 2.
2. **Finite off-line support (B13).** Finitely many off-line zeros implies RH. This is strictly weaker than AAL.

   That world already has Lindelöf, quasi-RH, finite index, a vanishing inner field and a rigid finite oscillation, with remainders down to `x^{Θ₂+ε}`.
3. **ZAL ⇒ RH**, equivalently ZAL ⇒ AAL. This lies strictly between the previous two. In that world the top is attained and `Θ∞ = ½`.
4. **Slow aligned returns (B89).** Exhibit or exclude, at a right zero, aligned returns with polynomial bounds on a disc right of the line, in a stated class of configurations. Done at every right zero, this is AAL.
5. **The tail law at the Kronecker scale (B96).** A conditional law of the Euler tail at one moment past `y ≍ log T`. Its off-diagonal is a count of shifted smooth × prime products: a binary prime problem not implied by RH.
6. **The lag versus a strip.** Decide whether the lag hypothesis of 8.2 is weaker than a zero-free strip for `ζ`.
7. **Long-shift jet correlations.** At a rightmost zero, prove a limit other than `m²` using the high-height zero-free region. This would prove AAL, and NAT if it uses only attainment.
8. **Integer-norm one-offs.** Construct a positive integer-norm Beurling system with a finite top layer, or prove that count distance below a stated threshold forbids one.
9. **The carry contradiction.** Decide whether `⌊x⌋` can coexist with a finite oscillation of `ψ`.
10. **Stepanov over `ℤ`.** A one-sided bound for `Φ` along one geometric progression. There is no analogue over `ℤ` of `x ↦ x^q`.
11. **Extremal law.** Which further property of `Q` contradicts the extremal position at a maximal-angle zero: order `½`, log-concavity of its coefficients, or the functional equation? This is adjacent, at RH level.
12. **Sub-power samplings.** Does any integer-lag sampling with sub-power gaps decide RH without ZAL? Adjacent.

**How the faces compare.**
- **Transport and recurrence** reformulate the problem: producing a return is producing a zero.
- **The lag and the jets** carry content. They aim at NAT, and each needs an unconditional input at power precision: a one-sided prime bound on scales of density one, or a long-shift correlation of `Λ`.
- **Count distance and carries** test integrality directly. Integrality is the property that every AAL-violating Euler-product model lacks.
- **No face has a tool that reaches it.**

---

## 10. What a proof cannot be, and what it must be

### A proof of AAL cannot

1. use only positivity of the primes, an Euler product and a smooth count (continuous Beurling one-offs);
2. use only discreteness of the primes with an Euler product (discrete one-offs);
3. use only the functional equation, order, reality and vertical asymptotics (`ξ_β`, zero relocation);
4. be stable under the heat flow at small positive time;
5. rest on exact identities, linear or nonlinear in `Λ`;
6. rest on diagonal decay of moments;
7. rest on typical-height or density-one information;
8. rest on large-height receivers alone, since they read only `Θ∞`;
9. rest on unconditional estimates of `ψ`, the Mertens function or the Liouville sum, since none reaches precision `x^Θ`;
10. rest on the random Euler model;
11. rest on repulsion technology, which isolates exceptional zeros;
12. rest on recurrence of the primes or on transport alone;
13. rest on size bounds on discs crossing `Re s = ½`;
14. rest on extremal-position inequalities alone;
15. rest on count distance alone.

### A proof of AAL must

1. **Couple heights.** It must carry information from one zero at bounded height to infinitely many heights. AAL compares `Θ`, which sees bounded heights, with `Θ∞`, which does not. Mechanisms that link heights are the explicit formula (a finite layer dominates `ψ` at every large `x`), dilations, vertical recurrence and Dirichlet alignment of phases.
2. **Use the Dirichlet series over `ℕ`**, with an input that fails on the Beurling one-offs: integer norms `N(x) = ⌊x⌋`, or the exact functional equation through its Beurling rigidity.
3. **Be an inequality, not an identity.** If it argues by contradiction, it may use the whole world of section 4, including the quasi-RH-level regularity at large heights and the rigid finite oscillation.
4. **Be clear whether it proves NAT or exactly AAL.** If it is attainment-based, it must identify the real point at which the attained top is detected.
5. **Place its scales** against the Kronecker scale `log T`, the head resolution `1/log y`, the Vinogradov–Korobov length and the diagonal range.
6. **Fail, through a named property, on every model of 6.1.**

### Questions to put to a proposed argument

- Where does the property of `ζ` enter that fails for each model of 6.1?
- Is any step an exact identity? If so, it is a boundary condition and not the inequality.
- At what precision does the contradiction occur, and what unconditional fact supplies that precision?
- How does information at the height of the top layer reach large heights?
- Is the argument stable under the heat flow?
- Does it confuse attained with non-attained tops, or the case `h = 0` with `h > 0`?

---

## 11. Milestones

1. Finitely many off-line zeros imply RH.
2. ZAL implies RH.
3. AAL for a restricted class of top layers: a single simple conjugate pair, or a gap `Θ − Θ₂` above a stated bound.
4. A slow aligned return at one right zero, exhibited or excluded in a stated class.
5. A conditional tail law at one moment past the Kronecker scale.
6. A decision whether the lag hypothesis is weaker than a strip.
7. A positive integer-norm one-off, or a count-distance threshold that forbids it.

---

## 12. Where it lives in the corpus

| Topic | Lean modules (under `formal/GaloisForLFunctions/`) | Key declarations |
|---|---|---|
| Definition, split, weak recurrence | `RHTower/ZetaWeakRecurrenceLadderCollapse` | `AsymptoticAbscissaLaw`, `riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw`, `riemannHypothesis_iff_zerosApproachLine_and_zeroDiscWeaklyRecurrent` |
| `Θ∞`, spectral gap, annihilator, twisted functional equation | `ZeroConfigurationGeometry/AsymptoticAbscissaSpectralGapAndTopAnnihilator` | `zetaAsymptoticAbscissa`, `asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_eq_zetaZeroAbscissa`, `not_asymptoticAbscissaLaw_iff_bilateral_spectralGap` |
| Finite oscillation and its rigidity | `ZeroConfigurationGeometry/TheOneOffsAreFiniteOscillationsOfThePrimeError`, `…/PrimeErrorFiniteOscillationRigidityAndSignChanges` | `PrimeErrorIsFiniteOscillation`, `not_asymptoticAbscissaLaw_iff_primeErrorIsFiniteOscillation`, `exists_primeErrorFiniteOscillation_of_lt_gap` |
| Dilation annihilation | `ZeroConfigurationGeometry/MultiplicativeDilationAnnihilationOfPrimeError` | `not_asymptoticAbscissaLaw_iff_twoPrime_dilationAnnihilation` |
| Jets, correlations, high zero-free region | `ZeroConfigurationGeometry/{FiniteExceptionalLayersForcePersistentLowJets, FiniteExceptionalLayersGiveHighZeroFreeJetBounds, HighDerivativesRecoverARightmostZero, FinitePoleJetsDecayAwayFromTheirHeight, VonMangoldtShortShiftCorrelationsVanish, TheHorizontalJetGainHasASharpGapCeiling}` | `not_asymptoticAbscissaLaw_has_positive_limit_after_short_shifts`, `not_asymptoticAbscissaLaw_has_high_jet_bounds` |
| Attainment producers | `RHTower/{AsymptoticAbscissaLawProducers, WeilLagFunctionFiniteMeasureExcursion, WeilLagFunctionDensityZeroExcursion, WeilLagProgressionZerosApproachLine, WeilLagFunctionProgressionBaire, WeilLagAsymptoticAbscissa, CrossRouteReceiverBridges, JointAncestryTypicalAsymptoticAbscissa, PolarGroundEnergySubexponentialZerosApproachLine}`, `ArithmeticKreinLangerTheory/PrimeTowersAndConeCouplingProduceAsymptoticAbscissaLaw`, `arithmetic-positivity-theory/FactorialTentDepthGapClusterAndPolarGraphBridge` | `riemannHypothesis_tfae_of_asymptoticAbscissaLaw` (collapse atlas) |
| Transport | `ArithmeticAuxiliaryDynamics/{TheMissingInputOfTransport, TheTransportOfAZeroIsEffective, TheSlowReturnBoundLivesRightOfTheLine, TheTransportCountOfAZero}` | `asymptoticAbscissaLaw_of_slowReturns_right`, `asymptoticAbscissaLaw_of_infinite_zeros`, `volume_returnSet_le_zeroCount` |
| Tail of a return | `TailArithmeticOfThePrimeOrbit/` (README §5, §10) | `exists_returns_tailBad_and_rare`, `tail_recurrence_dichotomy` |
| Recurrence, inner field | `ArithmeticInnerFunctionTheory/TheZeroOneLawOfRecurrence`, `RHTower/{ZetaRecurrenceAtEveryPointModuloItsZeros, ZetaStrongRecurrenceReceiver}` | `zero_free_or_infinite_of_recurrent`, `exists_zeta_recurrence_modulo_zeros` |
| Models | `ArithmeticPositiveDuality/{BeurlingOneOffZeroCountermodelsAndDefectTradeoff, ADiscreteBeurlingOneOff, SymmetricRationalZeroRelocationBohrObstruction, SmallIntegrableDefectsForceTheRationalPrimes}`, `RigidArithmeticOfCuts/{ABoundedCountWithANewZero, TheExtremalLawHasAModel}`, `SumProductArithmeticOfTheLogarithm/{PositiveNearCountEuler, LogarithmicCountFloor, CountDistanceRigidity}` | — |
| Cuts, carries, extremal zero | `RigidArithmeticOfCuts/` (README §5, §9) | — |
| Pipeline cards | `docs/drafts/pipeline/5-failed/aal-asymptotic-abscissa-law.md`, `1-in-progress/pnt-error-single-finite-oscillation.md`, `1-in-progress/rh/riemann-hypothesis-general/rh-big-picture-interpretation.md` (addenda 2–8) | — |

---

## 13. Classical background

- **Landau's theorem.** A Dirichlet integral of a nonnegative measure is singular at the real point of its abscissa. It is the mechanism of every attainment argument and of every failed floor argument.
- **Ω-theorems.** `ψ(x) − x = Ω±(x^{Θ−ε})`, and `Ω±(x^Θ)` when the top is attained. Littlewood: `Ω±(√x log log log x)`.
- **Bohr–Landau.** Zeros right of `½ + δ` have density zero among all zeros. Zero-density estimates count zeros up to height `T` and cannot see a bounded finite set.
- **Value distribution and universality.** Bohr–Jessen value distribution. Borchsenius–Jessen: `a`-points of positive density for `a ≠ 0`. Voronin universality for nonvanishing targets. Bagchi: strong recurrence is equivalent to RH.
- **Zero-free regions.** de la Vallée Poussin and Vinogradov–Korobov.
- **Exceptional zeros.** Siegel zeros and the Deuring–Heilbronn phenomenon: the classical picture of an isolated exceptional zero.
- **Selberg zeta functions.** Exceptional eigenvalues give finitely many real zeros in `(½, 1)`.
- **Davenport–Heilbronn and Voronin.** Abundant off-line zeros without an Euler product.
- **The heat flow.** Ki–Kim–Lee: finitely many nonreal zeros of `H_t` for `t > 0`. Rodgers–Tao: `Λ ≥ 0`. The real-rooted times form a closed half-line.
- **Numerical verification.** Platt–Trudgian: RH up to height `3·10¹²`.
- **Function fields.** Weil, and Stepanov's elementary proof.
