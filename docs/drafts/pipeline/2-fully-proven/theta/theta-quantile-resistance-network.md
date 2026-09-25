# Theta quantile action is an electrical potential kernel

- **ID:** theta-quantile-resistance-network
- **Stage:** 2-fully-proven (paper)
- **Type:** THEOREM (paper); spectral orientation remains open
- **Routes:** TQFQ, WS2, SQB, and theta source transport
- **Source:** The literal completed-theta density, its quantile profile, and the [CDF-action quotient](../1-in-progress/theta-quantile-fourier-action-quotient.md). The [critical one-port theorem](theta-quantile-critical-one-port-rigging.md) supplies the exact quantile boundary functional.
- **Statement:** The Fourier coefficients of reciprocal quantile speed are positive jump conductances; the CDF action is their potential kernel, and each column of the Xi-bearing compact inverse is the voltage of a dipole in this network.

## Why this changes the proof problem

The quotient's cross-frequency matrix was previously a list of differences of CDF actions. It is exactly a **dipole-response operator** for one source-defined, reversible, long-range electrical network. Network positivity and reciprocity apply to the *grounded* voltage differences. The Xi determinant instead uses the voltage gauge that decays at frequency infinity. Moving between those gauges adds a constant sequence, outside the operator's `ℓ²` space. Thus the remaining RH problem is a source-specific **boundary-gauge orientation** for a positive network, not a search for positivity of each Fourier block.

This is a reinterpretation and an exact source theorem, not an RH proof. It makes the whole cross-frequency coupling indispensable: the network Green equation and the compact inverse's exact zero mode require all frequencies simultaneously.

## Potential-kernel theorem

Let `h:[0,1]→[0,∞)` be continuous, symmetric about `1/2`, strictly positive on `(0,1)`, with `h(0)=h(1)=0`. Assume its nonzero Fourier coefficients

```text
  ĥ(n) = ∫₀¹ h(t) cos(2πnt) dt
```

are strictly negative and all actions

```text
  Φ_m = ∫₀¹ [1−cos(2πmt)]/h(t) dt,    Φ_0=0
```

are finite. These assumptions hold for the literal theta quantile profile: `h(t)=k(Q(t))/M`, `1/h=Q'`; [strict log-concavity and the exact curvature identity](../1-in-progress/theta-quantile-fourier-action-quotient.md#two-curvature-laws-and-the-candidate-jump) give `ĥ(n)<0`, and the theta tails give finite actions.

Set `a_n=−ĥ(n)>0` for `n≥1`. Then

```text
  ∑_{n≥1} a_n = ĥ(0)/2,
  h(t) = 2∑_{n≥1} a_n[1−cos(2πnt)]                 (1)
```

with absolute uniform convergence. Define the symmetric jump Laplacian on bounded integer sequences, and on the potential sequence below, by

```text
  (L_a f)_m = ∑_{n≥1} a_n[2f_m−f_{m−n}−f_{m+n}]. (2)
```

Its Fourier symbol is exactly `h`. The actions obey the **unit-capacity law** and the **point-source Green law**

```text
  2∑_{n≥1} a_n Φ_n = 1,                           (3)
  (L_a Φ)_m = −1_{m=0}       for every m∈ℤ.         (4)
```

All sums in (1), (3), and (4) converge absolutely; (2) does so on bounded sequences and on `Φ`. If current `+1` enters node `n` and `−1` leaves node `0`, its finite-energy voltage profile is

```text
  v_m^(n) = Φ_m−Φ_{m−n},       L_a v^(n)=δ_n−δ_0. (5)
```

For the literal theta source, the established `Φ_m∼log log |m|` asymptotic implies `v_m^(n)→0` as `|m|→∞`; this fixes the decaying gauge. The voltage drop is `v_n^(n)−v_0^(n)=2Φ_n`, so the effective resistance between `0` and `n` is `2Φ_n`. The [exact CDF matrix](../1-in-progress/theta-quantile-fourier-action-quotient.md#paper-proved-structural-reduction) therefore reads

```text
  D_(m,n) = v_m^(n)/(2πn),       m,n≠0.           (6)
```

For the full theta inverse `B`, the same formula includes row `m=0`; that row is its pinned-mean port. Equation (6) identifies the exact Xi divisor as the nonzero reciprocal spectrum of a dipole response, by the already proved determinant bridge. No zero or RH premise enters (1)–(6).

### Proof

The Fejér means of the Fourier series of `h` converge to `h(0)=0`. Since every `ĥ(n)=-a_n<0`, monotone convergence in those means gives `2∑a_n=ĥ(0)`. Absolute convergence follows, and Fourier uniqueness yields (1) uniformly.

Every summand in (1) is nonnegative. Tonelli therefore gives

```text
  2∑ a_n Φ_n
    = ∫₀¹ [2∑ a_n(1−cos(2πnt))]/h(t) dt
    = ∫₀¹1 dt = 1.
```

For fixed `m`, the integrand of each difference in (2) is

```text
  2(1−cos mt)−(1−cos(m−n)t)−(1−cos(m+n)t)
    = −2cos(mt)(1−cos nt),
```

where `cos jt` abbreviates `cos(2πjt)`. Its absolute value is at most `2(1−cos nt)`. Equation (3) thus justifies exchanging the sum and integral. Applying (1) gives

```text
  (L_a Φ)_m = −∫₀¹ cos(2πmt) dt = −1_{m=0}.
```

Translation invariance gives (5). The voltage difference follows from `Φ_0=0` and `Φ_{-n}=Φ_n`. Formula (6) is the existing theta quotient matrix, now interpreted as (5). For the theta profile, the Fourier coefficients are strictly negative by the source's proved strict log-concavity/curvature identity, so the abstract theorem applies.

## Score projection and the exact boundary gauge

There is a second exact description of the same source. Put `q=Q'=1/h`, `s=−h'`, `H₀={f∈L²(0,1):∫f=0}`, `Vf(t)=∫₀ᵗf`, `P` the mean-zero projection, `B=i M_q V`, `D=P B|H₀`, `T=P M_h P|H₀`, and `A=i P V|H₀`. Theta tails make `Q,s∈L²`; in physical coordinates this is `∫x²k(x)dx<∞` and `∫k'(x)²/k(x)dx<∞`. Indeed, the leading theta atom gives `k(x) ≍ exp(9x/2−π exp(2x))` and `|k'(x)/k(x)|=O(exp(2x))` on the positive tail; evenness handles the negative tail. The endpoint products `Qh` vanish. Integration by parts and `Q'h=1` give

```text
  ∫₀¹ Q(t)s(t)dt = 1,
  β(f)=∫₀¹Bf = −i∫₀¹Q(t)f(t)dt,
  A s = −i P h.
```

Consequently

```text
  Πf = f−s∫₀¹Qf,      Π²=Π,
  ran Π = Q⊥,          ker Π = span{s},
  T D = A Π,           ker D = span{s}.          (7)
```

For the last kernel equality, `D s=0` follows from `V s=−h` and `q h=1`. Conversely `D f=0` makes `qVf` constant; then `Vf` is a multiple of `h`, and differentiation makes `f` a multiple of `s`. This is an exact infinite-frequency cancellation: every isolated `{n,−n}` block of `D` has nonzero eigenvalues, yet their full coupling has the zero vector `s`.

Equation (7) is an oblique **Stein-score projection**. The quantile `Q` is the input coordinate, `s=−(log k)'∘Q` is the location score, and their pairing equals one. The positive network's grounded covariance kernel is

```text
  K(m,n)=Φ_m+Φ_n−Φ_{m−n},
```

whereas (6) uses `K(m,n)−Φ_n`. Positivity of `K` follows directly by writing its quadratic form as the integral of `|∑_m c_m(1−exp(2πimt))|²/h(t)` for finitely supported charges `c`. The missing constant is the gauge shift between grounded and decaying voltage. It is not an `ℓ²` vector, so positivity of `K` cannot be transported to `D` by dropping it. Indeed, every normalized Xi eigenmode has nonzero pinned-mean charge by the [critical one-port theorem](theta-quantile-critical-one-port-rigging.md); the uncharged positive response does not contain those modes. In physical coordinates that theorem also proves the quantile input is unbounded in the flat metric completion, and the original two-ended theta domain selects the actual Xi divisor.

### Kron reduction exposes the universal clock port

Short the positive network multiplier `M_h` over the constant Fourier mode. Write `h₀=∫₀¹h>0`, `b=P h`, and

```text
  G = T−(b⊗b)/h₀,
  γ(f)=∫₀¹ iVf(t)dt = i∫₀¹(1/2−t)f(t)dt.
```

For mean-zero `f`, `⟨f,Gf⟩=∫h|f|²−|∫hf|²/h₀` is a weighted variance. It is strictly positive for nonzero `f`, although `G` is not bounded below. The full identity `M_h B=iV`, decomposed into its constant and mean-zero Fourier rows, gives

```text
  T D=A−bβ,             ⟨b,Df⟩+h₀β(f)=γ(f),
  G D=A−(b/h₀)γ.                                  (8)
```

Thus the singular quantile input `β` disappears from the *formula* after network shorting: the remaining input `γ` is the universal linear clock, while the source enters through the positive shorted metric `G` and output vector `b`. In integer Fourier coordinates, `b_n=−a_|n|` and `γ(e_n)=−1/(2πn)`. Hence (8) reads

```text
  (G D)_(m,n)=1_{m=n}/(2πn)−a_|m|/(2πn h₀),
                       m,n≠0.                     (9)
```

This is an exact Schur-complement law, not a self-adjoint similarity. Its defect is one outer product of the theta conductance vector with the universal signed clock vector. The clock functional remains singular in the `G` energy: its density `1/2−t` has different nonzero endpoint values while `1/h=Q'` has infinite integral at both endpoints. Shorting changes the coordinates of the hard boundary condition; it does not erase it. Any hypothetical nonreal eigenmode `Df=μf` must have `γ(f)≠0`, since `γ(f)=0` in (8) would give `μ⟨f,Gf⟩=⟨f,Af⟩∈ℝ`.

For an actual divisor eigenmode `Df=−z⁻¹f`, writing `z=u+iv` and taking the imaginary part of (8) gives the exact boundary-work law

```text
  [v/|z|²]⟨f,Gf⟩ = −[1/h₀] Im(γ(f)⟨f,b⟩).     (10)
```

The left side is strictly oriented by `v`; the right side is the source conductance/clock phase that a proof must control. Equation (10) is a receiver, not an independent sign theorem.

For the normalized root primitive `g` of the [variogram pencil](../1-in-progress/theta-one-port-variogram-pencil.md#exact-chirality-of-the-actual-root-primitive), put `I(z)=∫₀¹g` and `E(z)=∫₀¹q|g|²`. Its equation `g'+1=−izqg` gives `γ(g')=iI(z)` and `∫h g'=−h₀−izI(z)`. Direct substitution into the variance defining `G` yields

```text
  ⟨g',Gg'⟩=|z|²[E(z)−|I(z)|²/h₀].               (11)
```

Consequently (10) is exactly the already known `Re I(z)=v E(z)` after the common `v|I|²/h₀` term cancels. The shorted identity locates the boundary channel but supplies no independent root exclusion. A source-specific theorem must constrain the left/right connection coefficient before imposing `Xi(z)=0`; applying positivity only to the already selected root repeats the universal energy law.

## Hard obstacle and next test

The network theorem proves source occurrence, positive conductances, exact resistance reciprocity, and capacity saturation. It does **not** prove that the decaying-gauge dipole operator has real nonzero spectrum. Generic even strictly log-concave densities also give positive conductances and (1)–(9), while the two-Gaussian source in the [CDF-action quotient](../1-in-progress/theta-quantile-fourier-action-quotient.md#two-curvature-laws-and-the-candidate-jump) has off-real Fourier zeros. The source-specific missing law must therefore control how the literal theta modular/prime structure transports the grounded positive response through the non-`ℓ²` boundary gauge.

A finite-section conjecture asked for positive mixed Stieltjes weights after whitening the metric. Equation (8) identifies why an ordinary finite positive spectral measure is not a closed route: both the original quantile input and the shorted clock input are unbounded in their respective energy completions. Their limiting bulk has continuous real spectrum; Xi modes are selected by the stronger two-ended theta domain. The next test must act on the [left/right connection coefficient](../1-in-progress/theta-one-port-variogram-pencil.md#positive-half-transform-and-the-actual-connection-problem) while retaining the modular atom assembly. The network formula (9) supplies exact conductance and clock legs for that test. A source-derived phase or boundary-domain law excluding nonreal connections would orient the Xi divisor; another finite mixed-moment sign without a domain passage would not.

## Gates

- [x] 0 → 1: source-pure theorem and exact divisor interface.
- [x] 1 → 2: paper proof of (1)–(11), with source conditions identified above.
- [ ] 2 → 3: formalize the theta specialization, including the Fourier action Green law and score projection, with foreground targeted Lean checks.
- [ ] 3 → 4: external novelty audit and standalone mathematical exposition.
