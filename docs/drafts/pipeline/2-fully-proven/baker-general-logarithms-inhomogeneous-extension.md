# Baker's theorem for arbitrary algebraic logarithms, including the inhomogeneous extension

- **ID:** `baker-general-logarithms-inhomogeneous-extension`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (Lean), `[LITERATURE]` / `[BRIDGE]`
- **Statement:** If `λ₁, …, λₙ ∈ ℂ` are `ℚ`-linearly independent and every `exp λᵢ` is algebraic, then `1, λ₁, …, λₙ` are linearly independent over `algebraicClosure ℚ ℂ`.

## Goal

Formalize Baker's full qualitative theorem, not only the existing distinct-prime specialization.
The public capstone must be a closed theorem proving a universally quantified `Prop`; its only
conditions are Baker's standard mathematical conditions (`exp λᵢ` algebraic and `ℚ`-linear
independence).  It must consume no route premise, imported Baker proposition, extra axiom, or
unproved hypothesis.

Planned public surface:

```lean
def IsLogarithmOfAlgebraic (λ : ℂ) : Prop := IsAlgebraic ℚ (Complex.exp λ)

def BakerTheorem : Prop :=
  ∀ (n : ℕ) (λ : Fin n → ℂ),
    (∀ i, IsLogarithmOfAlgebraic (λ i)) →
    LinearIndependent ℚ λ →
    LinearIndependent (algebraicClosure ℚ ℂ)
      (fun j : Option (Fin n) => Option.elim (1 : ℂ) λ j)

theorem bakerTheorem_holds : BakerTheorem
```

The homogeneous theorem and transcendence of every nonzero algebraic-coefficient linear form in
logarithms are corollaries of this inhomogeneous capstone.

## Gates

- [x] 0 → 1 in-progress: exact statement frozen; internal corpus, failed routes, and primary theorem statement audited
- [x] 1 → 2 fully-proven: complete dependency-closed paper proof, including zero estimate and parameter inequalities
- [ ] 2 → 3 formalized: exact Lean theorem, umbrella wiring, targeted checks, axiom audit, formal lint

## Frontier

- `[CORPUS]` `GaloisForLFunctions.RHTower.gelfondSchneider_holds` proves full complex
  principal-branch Gelfond--Schneider unconditionally in
  `formal/GaloisForLFunctions/RHTower/GelfondSchneider.lean`.
- `[CORPUS]` `GaloisForLFunctions.RHTower.bakerLinearIndependence_holds` proves
  algebraic-coefficient independence only for real logarithms of distinct rational primes in
  `formal/GaloisForLFunctions/RHTower/BakerProof/BakerIteration.lean`.
- `[CORPUS]` Existing Baker modules supply finite number-field containment, integral scaling,
  Siegel kernels, multipoint Schwarz extrapolation, algebraic-norm discreteness, and long parameter
  iteration.  Their relation type and terminal Vandermonde step are prime-specific.
- `[LITERATURE]` Baker's 1966 theorem and Waldschmidt's complete exposition state: for arbitrary
  chosen `λᵢ` with algebraic `exp λᵢ`, `ℚ`-linear independence of the `λᵢ` implies
  `algebraicClosure ℚ ℂ`-linear independence of `1, λ₁, …, λₙ`.
- `[OPEN CORE]` Formalize the nonhomogeneous auxiliary polynomial and a terminal zero estimate for
  exponential polynomials with distinct frequencies.  Natural-sample Vandermonde from the prime
  proof is insufficient: different chosen logarithm branches can have the same exponential.

## Paper-proof route

Assume a minimal counterexample and solve its nonzero algebraic relation for

```text
λₙ = β₀ + β₁ λ₁ + ··· + βₙ₋₁ λₙ₋₁.
```

Attach to an integral polynomial `P(Y₀,…,Yₙ)` the entire function

```text
G(z) = P(z, exp(z λ₁), …, exp(z λₙ)).
```

Use the relation to define `n` commuting algebraic differential operators.  Their iterates express
ordinary derivatives of `G` as polynomials in `λ₁,…,λₙ₋₁` with algebraic exponential-polynomial
components `G_σ`.  A Siegel kernel makes `G_σ(s)=0` in an initial derivative/sample box.  Multipoint
Schwarz plus algebraic-norm discreteness extrapolates to a larger sample box with smaller derivative
box.  Iterate far enough to contradict Tijdeman's zero bound for a nonzero exponential polynomial
with distinct frequencies.  Distinctness follows from `ℚ`-linear independence of the chosen
`λᵢ`, so the argument remains valid when `exp λᵢ` are multiplicatively dependent because of branch
  shifts.

Primary references audited:

- A. Baker, *Linear forms in the logarithms of algebraic numbers I*, Mathematika 13 (1966),
  DOI `10.1112/S0025579300003971`.
- M. Waldschmidt, *Linear Independence Measures for Logarithms of Algebraic Numbers*, Lecture Notes
  in Mathematics 1819 (2003), Lecture 3, especially the long extrapolation proof replacing the
  Philippon estimate by Tijdeman's zero estimate.
- R. Tijdeman, *On the number of zeros of general exponential polynomials*, Indagationes
  Mathematicae 33 (1971), DOI `10.1016/S1385-7258(71)80003-3`.

This is the long-extrapolation variant of Waldschmidt, *Linear Independence Measures for Logarithms
of Algebraic Numbers*, Lecture 3, §§3.1--3.3.  Philippon's algebraic-group zero estimate is avoided;
the terminal obligation is Tijdeman's one-variable exponential-polynomial zero estimate.

## Dependency-closed proof

Fix `n ≥ 1`, logarithms `λ : Fin n → ℂ`, algebraic numbers `αᵢ = exp λᵢ`, and assume that the
`λᵢ` are `ℚ`-linearly independent.  Suppose, for contradiction, that

```text
a₀ + a₁ λ₁ + ··· + aₙ λₙ = 0
```

is a nonzero relation with algebraic coefficients.  The logarithmic coefficients cannot all
vanish, since then `a₀ = 0`.  After reindexing, `aₙ ≠ 0`; put

```text
λₙ = b₀ + b₁ λ₁ + ··· + bₙ₋₁ λₙ₋₁,
b₀ = -a₀/aₙ,  bᵢ = -aᵢ/aₙ.
```

The finite set `{αᵢ, bᵢ}` lies in a number field `K ⊂ ℂ`: adjoining one algebraic element gives a
finite extension, and induction over the finite set plus the tower formula preserves finite
dimension.  Choose nonzero rational integers `c,d` such that every `c bᵢ` and every `d αᵢ` is an
algebraic integer.  This follows by clearing the leading coefficient of an integral polynomial for
each algebraic element, then multiplying the finitely many scales.

### 1. Scaled component operators

On `K[Y₀,…,Yₙ]`, define commuting operators

```text
E₀ = c ∂/∂Y₀ + (c b₀) Yₙ ∂/∂Yₙ,
Eᵢ = c Yᵢ ∂/∂Yᵢ + (c bᵢ) Yₙ ∂/∂Yₙ       (1 ≤ i < n).
```

They commute because their summands act on different variables or are commuting Euler operators.
For a polynomial `P`, a multi-index `σ : Fin n → ℕ`, and

```text
Gσ(z) = (E₀^σ₀ ··· Eₙ₋₁^σₙ₋₁ P)
          (z, exp(zλ₁), …, exp(zλₙ)),
```

the chain rule and the displayed expression for `λₙ` give

```text
c^ℓ Gσ^(ℓ)(z)
  = Σ_{|τ|=ℓ} multinomial(ℓ;τ)
      λ₁^τ₁ ··· λₙ₋₁^τₙ₋₁ G_{σ+τ}(z),                 (1)
```

where the factor belonging to coordinate `0` is `1`.  The case `ℓ=1` is the chain rule; induction,
commutativity of the `Eᵢ`, and the multinomial recurrence prove (1).  Consequently, a component
box `Gσ(s)=0` for `σᵢ<M` makes every component with `σᵢ<M'` vanish at each such `s` to ordinary
order at least `M-M'`, provided `2M'≤M`.

### 2. Auxiliary polynomial and initial zeros

Let `q` tend through sufficiently large multiples of `2^J`, where `J=2n²`, and set

```text
A = q^(2n+1),       B = q,
U = 2 q^(2n+1),     V = q^(2n-1).
```

Take polynomials with `Y₀`-degree `<U` and each exponential-variable degree `<V`.  There are

```text
C = U V^n = 2 q^(2n²+n+1)
```

coefficients.  Impose `Gσ(s)=0` for `0≤s<B` and `0≤σᵢ<A`; there are

```text
R = B A^n = q^(2n²+n+1) < C
```

rows.  Multiply the row at `(σ,s)` by `d^(s n(V-1))`.  Every matrix entry is then in `𝓞_K`: the
scaled operators have algebraic-integer coefficients, `s` is integral, and

```text
d^(s n(V-1)) ∏ᵢ αᵢ^(s tᵢ)
 = ∏ᵢ (d αᵢ)^(s tᵢ) · d^(s(n(V-1)-Σᵢtᵢ)).
```

The last exponent is nonnegative.  The already formalized number-field Siegel lemma
`GelfondSchneiderSiegel.exists_ne_zero_int_vec_house_le` therefore supplies a nonzero coefficient
vector in `𝓞_K` in this matrix kernel.

All constants below depend only on the fixed relation and `n`.  For a matrix row in the initial
box, elementary product, sum, derivative, and house estimates give

```text
log max(1, house(entry))
 ≤ C₁[A log q + U log(1+B) + V B].
```

Indeed, an `E₀` application contributes at most a fixed multiple of `U+V`, every other `Eᵢ`
contributes at most a fixed multiple of `V`, evaluation of `Y₀^k` contributes `(1+B)^U`, and the
conjugate exponential monomial contributes a fixed base to the power `nVB`.  Since `C=2R`, the
Siegel exponent `R/(C-R)` equals `1`.  Including row/column counts therefore yields

```text
log max_t house(η_t) ≤ C₂ q^(2n+1) log q.              (2)
```

The row scalars are nonzero, so the resulting nonzero polynomial `P` satisfies the unscaled initial
component equations.

### 3. Nonvanishing of the auxiliary entire function

Write

```text
G(z)=G₀(z)=Σ_t A_t(z) exp(ω_t z),
ω_t=Σᵢ tᵢ λᵢ,
```

with `deg A_t<U`.  Distinct exponent vectors give distinct `ω_t`, since a collision is a rational
(in fact integer) relation among the `λᵢ`.  A nonzero polynomial `P` has some nonzero `A_t`.

For completeness, polynomially weighted exponentials at distinct frequencies are linearly
independent.  If `Σ_j A_j(z)e^(ω_jz)=0`, fix `j` and apply

```text
∏_{k≠j} (D-ω_k)^(deg A_k+1).
```

Every `k`-term is killed.  On the `j`-term the result is `B_j(z)e^(ω_jz)`, where `B_j` is obtained
from `A_j` by products of `D+(ω_j-ω_k)`.  For nonzero `a`, `D+a` is injective on polynomials because
the top coefficient of `(D+a)Q` is `a` times the top coefficient of `Q`.  Hence `B_j≠0`, a
contradiction.  Thus `G` is not identically zero.

### 4. Uniform Tijdeman zero estimate

The required terminal estimate is proved here, without a frequency-gap denominator.

Let

```text
F(z)=Σ_{j<L} Σ_{k<K} f(j,k) z^k exp(u_j z),
```

be nonzero, with distinct `u_j` and `|u_j|≤Ω`; put `N=KL`.  For `R>0`, let `M(R)` be the maximum
of `|F|` on `|z|=R`, and let `h` be the number of zeros in `|z|≤R`, counted with multiplicity.
Factoring those zeros as `W(z)=∏(z-w_r)` and applying maximum modulus to `F/W` between radii `R`
and `4R` gives

```text
M(4R) ≥ M(R) (3/2)^h.                                  (3)
```

For the reverse bound, repeat each `u_j` exactly `K` times as nodes `η₀,…,η_{N-1}` and put

```text
Q(w)=∏_{v<N}(w-η_v),       ρ=2(Ω+1).
```

On the circle `|ζ|=ρ`, define the degree-`<N` polynomial

```text
H_z(w)=(2πi)⁻¹ ∮ e^(zζ) (Q(ζ)-Q(w))/((ζ-w)Q(ζ)) dζ
      = Σ_{m<N}p_m(z)w^m.                               (4)
```

The quotient `(Q(ζ)-Q(w))/(ζ-w)` is polynomial in `w`, so this definition is coefficientwise and
has no singularity at `w=ζ`.  Cauchy's formula rewrites it, for `|w|<ρ`, as

```text
H_z(w)=e^(zw)-Q(w)(2πi)⁻¹∮e^(zζ)/((ζ-w)Q(ζ))dζ.
```

The last integral is analytic in `w`.  Hence `e^(zw)-H_z(w)` is divisible analytically by `Q(w)`;
at every `u_j` its first `K` jets vanish.  Thus `H_z` is the required Hermite interpolant, including
at repeated nodes.  Applying the coefficient functional

```text
ℒ(Q)=Σ_{j,k} f(j,k) Q^(k)(u_j)
```

to these jet identities gives

```text
F(z)=Σ_{m<N} p_m(z) F^(m)(0).                           (5)
```

Write `Q(w)=Σq_kw^k`.  Its coefficient `ℓ¹` norm is at most `(1+Ω)^N`.  The coefficient of `w^m`
in the divided numerator is

```text
Σ_{k=m+1}^N q_k ζ^(k-1-m).
```

Since `ρ≥1`, its norm on the contour is at most `ρ^(N-1)(1+Ω)^N`, while

```text
|Q(ζ)| ≥ (ρ-Ω)^N = (Ω+2)^N.
```

The normalized circle length contributes `ρ`; therefore, for every `m<N`,

```text
|p_m(z)| ≤ ρ^N exp(ρ|z|).                               (6)
```

Cauchy's derivative estimate gives `|F^(m)(0)|≤m!M(R)/R^m`.  For `R≥1`, equations (5)--(6), on
`|z|=4R`, and `Σ_{m<N}m!≤N^(N+1)` imply

```text
M(4R) ≤ M(R) ρ^N exp(4ρR) N^(N+1).                     (7)
```

Since a nonzero entire function has `M(R)>0`, (3) and (7) give the closed, frequency-gap-free bound

```text
h log(3/2) ≤ 4ρR + N log ρ + (N+1) log N,              (8)
ρ=2(Ω+1).
```

This proof uses only polynomial coefficient bounds, Cauchy's formula/estimate, zero factorization,
and maximum modulus.  Existing corpus already contains finite Hermite CRT, analytic zero
orders/divisors, circle Cauchy estimates, and entire zero factorization.  The contour-interpolant
coefficient estimate (6) is the new analytic module; unlike a confluent Vandermonde inverse, it has
no denominator involving `min|u_i-u_j|`.

### 5. Long extrapolation

Define, for `0≤j≤J`,

```text
M_j = A/2^j,       S_j = q^(j+1).
```

These are integers because `2^J∣q`.  Initial construction gives
`Gσ(s)=0` for `σᵢ<M₀`, `0≤s<S₀`.  Suppose this holds at stage `j`.  For
`σᵢ<M_{j+1}`, identity (1) gives a zero of order at least
`M_j-M_{j+1}=M_{j+1}` at every old sample.  Apply multipoint Schwarz on the disk
`|z|≤4S_{j+1}`.  For a new integer `s<S_{j+1}` and every old node `r<S_j`,

```text
|s-r| / (4S_{j+1}-r) ≤ 2/3.
```

Consequently

```text
|Gσ(s)| ≤ max_{|z|=4S_{j+1}}|Gσ(z)|
             · (2/3)^(M_{j+1}S_j).                     (9)
```

From (2), the finite sum defining `Gσ`, and the component degree/frequency bounds,

```text
log max_{|z|≤4S_{j+1}} max(1,|Gσ(z)|)
 ≤ C₃[q^(2n+1)log q + q^(2n+j+1)].                    (10)
```

At an integer sample, `x=d^(s n(V-1))Gσ(s)` is an algebraic integer.  Applying every embedding of
`K` to its explicit finite algebraic expression gives the same upper exponent as (10), with another
fixed constant.  If `x≠0`, its field norm is a nonzero rational integer, so

```text
1 ≤ |x| · house(x)^[K:ℚ]-1.                            (11)
```

But the negative logarithm contributed by the Schwarz estimate is

```text
M_{j+1}S_j log(3/2)
 = q^(2n+j+2) log(3/2)/2^(j+1),                       (12)
```

which, for fixed `j≤J`, dominates both terms in (10) and the conjugate/denominator bounds by a
factor tending to infinity.  Thus (9)--(12) contradict (11) for every nonzero new value.  There
are only `J` stages, so one sufficiently large permitted `q` works simultaneously.  Induction
proves the stage-`J` component box.

### 6. Terminal contradiction

At each of the `S_J=q^(J+1)` integer samples, (1) makes `G` vanish to order at least
`M_J=A/2^J`.  Thus its zero count in `|z|≤S_J` is at least

```text
M_J S_J = q^(2n+J+2)/2^J.                             (13)
```

The exponential-polynomial expansion of `G` has at most `V^n` distinct frequencies, polynomial
degree `<U`, interpolation dimension `N≤UV^n=C`, and

```text
max_t |ω_t| ≤ V Σᵢ|λᵢ|.
```

The right side of the zero estimate (8), with `R=S_J`, is therefore bounded by a fixed constant
times

```text
q^(2n²+n+1) log q + q^(2n+J).
```

For `J=2n²`, the lower exponent in (13) is `2n²+2n+2`, strictly larger than
`2n²+n+1` and `2n²+2n`.  This contradicts (8) for sufficiently large `q`.  Hence the assumed
algebraic relation does not exist.

For `n=0`, the indexed family is the singleton `{1}` and is linearly independent because `1≠0`.
The contradiction above handles every `n≥1`, proving the inhomogeneous theorem.

### 7. Extension consequences

Restricting the `Option (Fin n)`-indexed independent family gives homogeneous independence of the
`λᵢ`.  If algebraic `βᵢ` give a nonzero form `Λ=Σβᵢλᵢ` and `Λ` were algebraic, then

```text
(-Λ)·1 + Σβᵢλᵢ = 0
```

would contradict the capstone; hence every nonzero algebraic-coefficient linear form is
transcendental.  Taking two logarithms recovers the arbitrary-branch Gelfond--Schneider
compatibility statement.

## Gelfond--Schneider dependency

Existing Gelfond--Schneider modules were checked with
`lake env lean GaloisForLFunctions/RHTower/GelfondSchneider.lean`.  `#print axioms` for
`gelfondSchneider_holds`, its real form, and `log_ratio_transcendental` reports only `propext`,
`Classical.choice`, and `Quot.sound`.  General Baker will retain these modules as base infrastructure
and expose Gelfond--Schneider as the two-logarithm corollary/compatibility theorem.

## Hostile audit

- Prime-only theorem does not imply this statement: arbitrary algebraic bases do not reduce to
  rational primes.
- Principal logarithms are insufficient: theorem quantifies over every chosen logarithm branch.
- `exp`-node Vandermonde is invalid in general.  Example frequencies `log 2` and
  `2 log 2 + 2πi` are `ℚ`-linearly independent although their exponentials are multiplicatively
  dependent.
- Homogeneous independence alone is weaker than requested extension.  Adjoining `1` is required to
  prove every nonzero algebraic linear form is transcendental, not merely nonzero.
- Effective Matveev bounds are a separate active card and are not silently claimed here.
- The proof never separates frequencies by a lower bound on `|ω_t-ω_u|`; such a bound is
  unavailable uniformly as the exponent box grows.  Contour interpolation uses only the upper
  frequency radius and is therefore stable under close frequencies.
- Nonvanishing is not imported from the prime Baker theorem.  It uses only the assumed
  `ℚ`-linear independence through distinct additive frequencies and the elementary annihilating
  differential-operator argument.
- Row integrality does not assume the algebraic bases are units.  The factor
  `d^(s n(V-1))` clears every nonnegative sample power uniformly; all samples are nonnegative.
- The Siegel matrix is genuinely nonzero: at `s=0`, `σ=0`, the constant-monomial column has entry
  `1`.  Thus the existing explicit number-field Siegel theorem applies directly.
- Parameter audit: columns are exactly twice initial rows.  At each fixed extrapolation stage,
  decay has exponent `2n+j+2`, one power above analytic/conjugate growth `2n+j+1`.  At the terminal
  stage `J=2n²`, zero multiplicity has exponent `2n²+2n+2`, above both the coefficient dimension
  `2n²+n+1` (even with `log q`) and exponential-type term `2n²+2n`.  These inequalities remain
  strict at the edge case `n=1`.

## Log

- 2026-08-15 — formalized first gap-free analytic dependency chain in
  `RHTower/BakerGeneralProof`: differential-operator nonvanishing for polynomial exponentials,
  contour Hermite interpolation at repeated frequencies, exact repeated-frequency modulus degree
  and coefficient/minimum-modulus estimates, time/frequency jet duality, exact initial-jet
  representation, four-radius multipoint lower growth, contour/Cauchy upper growth, and terminal
  maximum-modulus cancellation.  Targeted `.olean` checks close through `TerminalZeroEstimate`;
  every finished module is wired into `RHTower.lean`, whose full umbrella was deliberately not
  built.  Remaining formal core is algebraic component-operator/Siegel/extrapolation infrastructure
  and the final parameter contradiction/capstone.
- 2026-08-15 — card opened after kernel audit of existing Gelfond--Schneider and prime-Baker
  substrate.  Exact general and inhomogeneous statement frozen.  Terminal branch-collision defect in
  prime Vandermonde isolated as first formalization core.
- 2026-08-15 — dependency-closed proof completed and hostile-audited.  Replaced any frequency-gap
  argument by a contour Hermite interpolant, obtaining a uniform zero bound with harmless logarithmic
  loss.  Exact row/column, extrapolation, and terminal exponents close for every `n≥1`, including
  `n=1`; `n=0` is immediate.  Promoted to Stage 2 for Lean formalization.
- 2026-08-15 — formalized `BakerGeneralProof.ExponentialMonomial`: the exponential subalgebra is
  invariant under every solved component derivation, each bounded exponent monomial is a simultaneous
  eigenvector, and each component eigenvalue is an algebraic integer under the existing common
  component scale.  The module is wired into `RHTower.lean`; its source and targeted OLean audit
  close, and `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.  Next
  core: package the simultaneous-eigenvalue sample rows as an integral Siegel matrix.
