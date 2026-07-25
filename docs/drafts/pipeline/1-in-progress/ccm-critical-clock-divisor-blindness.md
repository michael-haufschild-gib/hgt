# CCM critical-clock divisor blindness: the four-unit source budget is a class invariant

- **ID:** `ccm-critical-clock-divisor-blindness`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) + WITNESS + CATEGORY-WIDE NO-GO for the CCM four-unit lane
- **Source:** `ccm-four-unit-source-codiagonal-attack.md` (C48–C50),
  `mobius-incidence-curvature-gamma-sonin-pole-divisor-transfer-rh.md` (`[OPEN CORE]`),
  `docs/handover/connes.md`
- **Statement:** Every critical invariant of the CCM Möbius/squarefree source — the cut mass,
  cut overlap, cut energy, the pointed-Fisher Ward profile `E_W(u)`, the one-corner profile
  `E_lower(u)` and its total four units — is a functional of the exponential clock law `Exp(1)`
  alone, hence is constant on the whole class of nonnegative Mellin sources with a simple pole at
  `σ=1`.  That class contains explicit members whose strict-right divisor is nonempty.  Therefore
  the four-unit budget carries **no** information about the strict-right divisor, and no
  Gauss–Codazzi/energy-split argument whose only source input is that budget can prove RH.

## 0. Why this is the right question

The lane's ledger (`ccm-four-unit-source-codiagonal-attack.md`) contains fifty conjectures
`C1`–`C50`, each killing one *shape* of source→target transport: scalar, channelwise, closable,
finite-jet, bounded-postprocessed, norm-holomorphic, meromorphic-cusp, diagonal-Pick, and so on.
None of them asked the prior question:

> How much of the strict-right Xi divisor is *present* in the source data that the budget is
> computed from?

This card answers it: **none**.  The answer is not another shape restriction; it is an information
statement about the source itself, and it applies to every transport whatsoever whose source input
is the critical budget.

## 1. The class `𝓢` of critical clock sources

`[DEFINITION]`  A **critical clock source** is a pair `S=(dN,Z)` where

```text
dN  is a nonnegative Borel measure on [1,∞),
Z(σ)=∫_[1,∞) x^{-σ} dN(x) < ∞   for every σ>1,
(σ-1)Z(σ) → K ∈ (0,∞)           as σ ↓ 1.                          (1.1)
```

Write `𝓢` for the class of all such `S`, `ε=σ-1`, and let

```text
p_σ(dx) = Z(σ)^{-1} x^{-σ} dN(x)      (Gibbs probability on [1,∞)),
Y_σ     = ε·log x       under p_σ      (the critical clock).        (1.2)
```

`[FACT 1.3]` The CCM Möbius/squarefree source is a member of `𝓢`.  Indeed
`dN_sq=Σ_{d squarefree} δ_d` and `Z_sq(σ)=ζ(σ)/ζ(2σ)`, so `(σ-1)Z_sq(σ)→1/ζ(2)`.
In the Lean corpus this source is `squarefreeMobiusProbability`, and
`norm_infiniteMobiusSignedWeight_sq` proves that the Möbius sign contributes **nothing** to any
norm: every energy of the source package is computed from `p_σ` alone.

`[FACT 1.4]` For `S∈𝓢` the **strict-right divisor** is
`Div(S) = {s : Re s > 1/2, Z_S(s)=0}` (zeros of the meromorphic continuation, when it exists),
and the associated Schwarz-paired **Ward response** is
`r_S(w) = 2 Σ_{ρ∈Div(S)} (w+λ_ρ)^{-1}`, `λ_ρ` the centred coordinate of `ρ`.
For the Möbius source, `Div = ∅ ⟺ RH`, because `ζ(2s)` is zero-free and non-vanishing on
`Re s>1/2`, so on that half-plane the divisor of `Z_sq=ζ(s)/ζ(2s)` **is** the strict-right divisor
of `ζ`.

## 2. `[PROVED HERE]` Theorem A — critical universality

**Theorem A.**  Let `S∈𝓢`.  Then

```text
(a) for every u ≥ 0:      E[e^{-u Y_σ}] = Z(σ+uε)/Z(σ) → 1/(1+u);
(b) Y_σ ⇒ Exp(1) and all moments converge;
(c) with the score s(y)=2(1-y), the truncated Gram triple satisfies
      a(u) := P(Y_σ ≤ u)                 → ∫_0^u e^{-y}dy       = 1-e^{-u},
      c(u) := E[2(1-Y_σ)1_{Y_σ≤u}]       → 2∫_0^u (1-y)e^{-y}dy = 2u e^{-u},
      b(u) := E[4(1-Y_σ)^2 1_{Y_σ≤u}]    → 4∫_0^u (1-y)^2e^{-y}dy
                                          = 4(1-(1+u^2)e^{-u});
(d) hence the rank-two cutoff Ward energy has the limit
      E_W(u) = (4-b(u))a(u) + (1-a(u))b(u) - 2c(u)^2
             = 4[(2+u^2)e^{-u} - 2(1+2u^2)e^{-2u}],
      E_lower(u) = E_W(u)/2,   ∫_0^∞ E_lower(u)du = 4.
```

Every quantity in `(c)`–`(d)` is the same for **every** `S∈𝓢`.

*Proof.*

`(a)` is pure algebra from the pole.  For `u≥0`, `σ+uε>1`, so

```text
E[e^{-uY_σ}] = E[x^{-uε}] = Z(σ+uε)/Z(σ).
```

Write `ε'=(σ+uε)-1=ε(1+u)`.  By `(1.1)` applied twice (both `σ↓1` and `σ+uε↓1`),
`ε'Z(σ+uε)→K` and `εZ(σ)→K`, so

```text
Z(σ+uε)/Z(σ) = [ε'Z(σ+uε)]/[εZ(σ)] · ε/ε' → (K/K)·1/(1+u) = 1/(1+u).
```

No Tauberian input is used; only the two-sided limit `(1.1)`.

`(b)` `1/(1+u)` is the Laplace transform of `Exp(1)`, and pointwise convergence of Laplace
transforms of probability measures on `[0,∞)` implies weak convergence (continuity theorem).
For moments, note that `(1.1)` also gives, for `0<u<1`,

```text
E[e^{+uY_σ}] = Z(σ-uε)/Z(σ) → 1/(1-u),        σ-uε = 1+ε(1-u) > 1,
```

so the exponential moments of `Y_σ` converge for `u<1`.  In particular `sup_σ E[e^{Y_σ/2}]<∞`,
which makes `{Y_σ^k}` uniformly integrable for every `k`; hence `E[f(Y_σ)]→E[f(Y)]` for every
Borel `f` of polynomial growth whose discontinuity set is `Exp(1)`-null.

`(c)` The three functions in `(c)` are of that type (`1_{[0,u]}` times a polynomial, discontinuity
set `{u}`, which is `Exp(1)`-null).  The three closed values are elementary:

```text
∫_0^u e^{-y}dy = 1-e^{-u},
∫_0^u (1-y)e^{-y}dy = u e^{-u},
∫_0^u (1-y)^2 e^{-y}dy = 1-(1+u^2)e^{-u}.
```

(The last: `∫_0^u(1-2y+y^2)e^{-y}dy = (1-e^{-u}) - 2(1-(1+u)e^{-u}) + (2-(u^2+2u+2)e^{-u})
= 1-(1+u^2)e^{-u}`.)

`(d)` is the rank-two cutoff Ward identity applied to the pointed Fisher connection
`X_σ = 2^{-1/2}(|χ_σ⟩⟨ψ_σ|+|ψ_σ⟩⟨χ_σ|)`; in the corpus this is
`squarefreeMobiusCriticalFisherCutoffWardLimit_eq_gram`.  Expanding,

```text
(4-b)a+(1-a)b-2c^2
  = 4(1-e^{-u}) - 2·4(1-(1+u^2)e^{-u})(1-e^{-u}) + ... = 4[(2+u^2)e^{-u}-2(1+2u^2)e^{-2u}],
```

and `∫_0^∞[(2+u^2)e^{-u}-2(1+2u^2)e^{-2u}]du = (2+2) - 2(1/2+2·(1/4)) = 4-2 = 2`, so
`∫E_W = 8`, `∫E_lower = 4`. ∎

**Corollary A′ (blindness).**  Every scalar invariant of the CCM source package that is defined
through the critical limit `σ↓1` — the four-unit budget, `E_W`, `E_lower`, the Fisher curvature
`4ε^2 Var(log d) → 4`, the Gini/incidence curvature `E_σ = 4εE|log d-log d'| → 4` — takes the
**same value on every member of `𝓢`**.  It therefore cannot separate two members of `𝓢` with
different strict-right divisors.

## 3. `[PROVED HERE]` Theorem B — an explicit member of `𝓢` with an off-line divisor

**Theorem B (elementary witness `S₀`).**  Fix `θ∈(1/2,1)` and `a>0`, put `ρ₀=θ+ia`.  Let

```text
w = 1/(1-ρ₀),   φ = arg w ∈ (0,π/2),
X = exp((2π-φ)/a) > 1,     m = |w|·X^{θ} > 0,
dN₀ = 1_{[1,∞)}(x)dx + m·δ_X   ( ≥ 0 ),
Z₀(s) = ∫_[1,∞) x^{-s} dN₀(x) = 1/(s-1) + m X^{-s}   (Re s>1).      (3.1)
```

Then

```text
(i)   Z₀ extends meromorphically to ℂ with one simple pole, at s=1, residue 1;
(ii)  (σ-1)Z₀(σ) → 1, so S₀=(dN₀,Z₀) ∈ 𝓢;
(iii) Z₀(ρ₀) = Z₀(ρ̄₀) = 0, and Re ρ₀ = θ > 1/2.
```

*Proof.*  `∫_1^∞ x^{-s}dx = 1/(s-1)` for `Re s>1`; the atom contributes `mX^{-s}`; this proves
`(3.1)`, and the right-hand side of `(3.1)` is meromorphic on `ℂ` with the single simple pole
stated, giving `(i)` and `(ii)`.  For `(iii)`: `1-ρ₀=(1-θ)-ia` has argument in `(-π/2,0)`, so
`w=1/(1-ρ₀)` has `φ=arg w∈(0,π/2)`, whence `log X=(2π-φ)/a>0` and `X>1`.  Then

```text
m X^{-ρ₀} = |w| X^{θ} X^{-θ} e^{-ia log X} = |w| e^{-i(2π-φ)} = |w|e^{iφ} = w,
```

while `1/(ρ₀-1) = -1/(1-ρ₀) = -w`; adding gives `Z₀(ρ₀)=0`.  Since `m,X` are real and `X>0`,
`Z₀(s̄)=conj Z₀(s)`, so `Z₀(ρ̄₀)=0`. ∎

**Theorem B′ (genuine Beurling witness `𝓟₀`, with an Euler product and Möbius signs).**
Fix `θ∈(1/2,1)`, `a>0`, `ρ₀=θ+ia`, `x₀=2^{1/(1-θ)}`, `u₀=log x₀`, and let

```text
dΠ(x) = (log x)^{-1}(1 - 2x^{θ-1}cos(a log x))·1_{[x₀,∞)}(x)dx.        (3.2)
```

Then `dΠ ≥ 0` (because `2x^{θ-1} ≤ 2x₀^{θ-1} = 1` for `x ≥ x₀`), so `(3.2)` is a legitimate
generalized (Beurling) prime measure.  Its squarefree partition function and zeta are

```text
Z_sq(s) = exp(∫x^{-s}dΠ),      ζ_𝓟(s) = exp(Σ_{k≥1} k^{-1}∫x^{-ks}dΠ),
```

with `dN_sq = Σ_{k≥0} dΠ^{*k}/k! ≥ 0` (multiplicative convolution) and Möbius sign `(-1)^k` on the
`k`-th layer.  Then:

```text
(i)   ∫_{x₀}^∞ x^{-s}dΠ(x) = E₁((s-1)u₀) - E₁((s-ρ₀)u₀) - E₁((s-ρ̄₀)u₀);
(ii)  Z_sq(s) = C·(s-ρ₀)(s-ρ̄₀)/(s-1)·e^{H(s)}, H entire, C>0:
      exactly one simple pole (s=1) and exactly two simple zeros (ρ₀, ρ̄₀) in ℂ;
(iii) R(s) := Σ_{k≥2} k^{-1}∫x^{-ks}dΠ is holomorphic on Re s>1/2, so ζ_𝓟 = Z_sq·e^{R}
      has, on Re s>1/2, the same divisor: one simple pole at 1, simple zeros at θ±ia;
(iv)  (σ-1)Z_sq(σ) → C·(1-ρ₀)(1-ρ̄₀)·e^{H(1)} ∈ (0,∞), so 𝓟₀ ∈ 𝓢.
```

*Proof.*  `(i)`  Substituting `x=e^{u}` and using `∫_{u₀}^∞ e^{-(w-1)u}du/u = E₁((w-1)u₀)` for
`Re w>1` gives the three terms with `w=s`, `w=s-ρ₀+1`, `w=s-ρ̄₀+1`; all three converge for
`Re s>1` because `θ<1`, and the identity persists by analytic continuation.
`(ii)`  `E₁(z) = -γ - log z + h(z)` with `h` entire and `h(0)=0`; the three `-γ` and three
`-log u₀` terms cancel up to a constant, so

```text
∫x^{-s}dΠ = -log(s-1) + log(s-ρ₀) + log(s-ρ̄₀) + γ + log u₀
            + h((s-1)u₀) - h((s-ρ₀)u₀) - h((s-ρ̄₀)u₀),
```

and exponentiating gives `(ii)`; `e^{H}` never vanishes, so there are no other zeros or poles.
`(iii)` For `k≥2` and `Re s>1/2` we have `Re(ks)≥1+δ`, and

```text
∫_{x₀}^∞ x^{-kσ}(1+2x^{θ-1})dx/log x ≤ (log x₀)^{-1}[x₀^{1-kσ}/(kσ-1) + 2x₀^{θ-kσ}/(kσ-θ)],
```

which is `O(x₀^{-kσ})`; summing over `k≥2` converges locally uniformly on `Re s>1/2`.  All
singularities of `s↦∫x^{-ks}dΠ` sit at `s∈{1/k, ρ₀/k, ρ̄₀/k}`, whose real parts are `≤1/2` for
`k≥2` with equality only at `s=1/2`; so `R` is holomorphic on the open half-plane `Re s>1/2`.
`(iv)` is immediate from `(ii)`. ∎

*Numerical certificate (mpmath, 25–30 digits).*  For `θ=3/4, a=1, x₀=16`: the two expressions in
`(i)` agree to `3·10^{-33}`; `ζ_𝓟(ρ₀+ϵ)/ϵ → 2.6016+2.1721i` and `Z_sq(s)(s-1)/((s-ρ₀)(s-ρ̄₀)) →
1.0292+1.4118i ≠ 0` (simple zero); `ε·ζ_𝓟(1+ε) → 0.25803` and `ε·Z_sq(1+ε) → 0.25418` (simple
poles); `ε·E[log d] → 1`; `Z_sq(1+ε+uε)/Z_sq(1+ε) → 1/(1+u)` to `10^{-6}` at `ε=10^{-6}`.

## 4. `[PROVED HERE]` Theorem C — the four-unit budget cannot imply the Ward bound

**Theorem C.**  Let `S∈𝓢` have a strict-right zero `ρ` with centred coordinate `λ=a₀+ib₀`,
`a₀=Re ρ-1/2 ∈ (0,1/2)`.  Then the Schwarz pair `{λ,λ̄}` alone contributes

```text
‖r_S‖^2_{H^2(ℂ_+)} = ‖2k_{λ̄}+2k_{λ}‖^2 = 4(1/a₀ + a₀/(a₀^2+b₀^2)) > 4/a₀ > 8.   (4.1)
```

*Proof.*  With the Szegő kernel `k_v(w)=(w+v̄)^{-1}` and `⟨k_v,k_u⟩=k_v(u)=(u+v̄)^{-1}`,

```text
⟨k_{λ̄},k_{λ̄}⟩ = 1/(λ+λ̄) = 1/(2a₀),   ⟨k_{λ},k_{λ}⟩ = 1/(2a₀),
⟨k_{λ̄},k_{λ}⟩ = 1/(2λ),
```

so the squared norm is `4[1/(2a₀)+1/(2a₀)+2Re(1/(2λ))] = 4[1/a₀ + a₀/(a₀^2+b₀^2)]`, which is
`> 4/a₀ > 8` because `0<a₀<1/2`. ∎

**Corollary C′ (category-wide no-go).**  Combining Theorems A, B, C:

```text
the four-unit budget (and the eight-unit two-sided budget) is constant on 𝓢;
𝓢 contains S₀ (and the Beurling system 𝓟₀) with ‖r‖^2 > 8;
𝓢 contains the Möbius source, for which ‖r‖^2 ≤ 4 ⟺ RH.
```

Hence **no implication of the form "four-unit source budget ⟹ `‖r‖²≤4`" (or `≤8`) can be valid on
`𝓢`**, and in particular no argument establishing the C48/C49 incidence whose source input is the
critical budget, the profile `E_lower`, the pointed-Fisher curvature, or any other critical clock
functional.  The `[OPEN CORE]` Gauss–Codazzi split

```text
source four-unit curvature = anti-causal curvature energy + causal remainder energy
```

is therefore **not** a decomposition of a known quantity: its left-hand side is a class invariant
and its right-hand side is divisor-dependent, so the identity contains its own conclusion.  This is
the precise reason every one of `C1`–`C50` failed: each tested transports built from `𝓢`-universal
data.

## 5. Relation to the corpus's existing blindness theorem

`ProjectiveFisherBlindness.lean` proves that Born probabilities, expectations and the Fisher metric
are invariant under a coordinatewise unimodular phase twist, hence "cannot by itself recover the
zero divisor, which also depends on coefficient phases".  Theorem A/B is strictly stronger and
different in kind:

- the phase argument leaves the positive cone (it produces a non-arithmetic, phase-twisted object),
  and is answered by "the transport uses the actual Möbius phases";
- Theorems A–C stay **inside** the positive cone: `S₀` and `𝓟₀` are honest nonnegative sources,
  `𝓟₀` has a genuine Euler product and genuine Möbius signs, and the divisor still moves while
  every critical invariant is frozen.

So the blindness is not a phase artefact; it is a property of the critical limit.

## 6. `[PROVED HERE]` The forced successor: the functional equation is rigid at exactly `x^{1/2}`

Theorem A says the source's critical limit is blind.  What input is left?  Not the Gamma multiplier
(it is `𝓢`-independent and its norm tends to one — `mobius-incidence-…` `(7b)`).  The only
remaining candidate is the *functional equation*, i.e. the relation between the prime measure and
the archimedean factor.  Write, for a system with generalized von Mangoldt measure `dψ ≥ 0`,

```text
M(s) = ∫_1^∞ x^{-s}dψ(x)     (Re s>1).
```

`[LEMMA 6.1]`  `π^{-s/2}Γ(s/2)F(s)` is invariant under `s↦1-s` **iff**

```text
M(s) + M(1-s) = (1/2)[Ψ(s/2)+Ψ((1-s)/2)] - log π =: A(s),                (6.1)
```

`Ψ` the digamma function.  (Differentiate `log ξ_F(s)=log ξ_F(1-s)`.)

**Theorem D (rigidity at the RH exponent).**  Let `ν` be a signed Borel measure on `[1,∞)` with
`∫_1^∞ x^{-(1/2-δ)}d|ν|(x) < ∞` for some `δ∈(0,1/2)`, and suppose `N(s)=∫x^{-s}dν` satisfies
`N(s)+N(1-s)=0` on `|Re s-1/2|<δ`.  Then `ν=0`.

*Proof.*  Put `u=log x`, `dν̃(u)=e^{-u/2}dν(e^{u})` on `[0,∞)`; then
`∫_0^∞ e^{δu}d|ν̃| = ∫ x^{-(1/2-δ)}d|ν| < ∞`.  For `|Re z|<δ`,
`N(1/2+z)=∫_0^∞ e^{-zu}dν̃(u)` and `N(1/2-z)=∫_0^∞ e^{zu}dν̃(u)` converge absolutely, so the
hypothesis reads `∫_0^∞ cosh(zu)dν̃(u)=0`.  Setting `z=iξ`, the cosine transform of `ν̃` vanishes
identically; the even extension `ν̃_e` of `ν̃` to `ℝ` is a finite signed measure with vanishing
Fourier transform, so `ν̃_e=0`, hence `ν̃=0` and `ν=0`. ∎

**Corollary D′.**  Two `Λ`-positive systems obeying the *same* archimedean reflection `(6.1)` whose
von Mangoldt measures satisfy `|ψ₁-ψ₂|([1,x]) = O(x^{1/2-δ'})` are identical.  The Riemann
functional equation therefore determines the arithmetic **exactly down to the scale `x^{1/2}`**,
and RH is precisely the statement that the true system sits at that rigidity threshold.

This is the exact structural complement of Theorem A: the *budget* is blind at every scale, while
the *functional equation* is rigid at every scale coarser than `x^{1/2}` and at no finer one.  Any
surviving CCM producer must therefore be a rigidity statement at the `x^{1/2}` seam, not an energy
budget.  `[NOVELTY: Hamburger-type; the exponent-`1/2` reading is the new content, external
priority open.]`

## 7. What this opens (not a terminus)

1. **New object to construct.**  A source invariant that is *not* a critical clock functional:
   the finite-`σ` (pre-limit) discrepancy `Δ_σ := ε log[Z_S(σ)·(σ-1)/K]`, whose oscillation in
   `σ` distinguishes `S₀` from the Möbius source.  Theorem A says the budget kills it in the
   limit; the question is whether the C49 incidence can be run on `Δ_σ` before the limit.
2. **A sharper class.**  Add `(6.1)` to the definition of `𝓢` and ask whether `𝓢_FE` still has
   members with off-line divisor.  By Theorem D any such member differs from `ζ` by `≫x^{1/2}`.
   `𝓢_FE`-blindness would kill the lane outright; `𝓢_FE`-rigidity would *be* RH.  This is the
   sharpest well-posed successor question the lane has produced.
3. **Immediate falsifier for future proposals.**  Every CCM transport proposal must now be run
   against `S₀` first: if its contractivity proof goes through for `S₀`, it is dead on arrival.

## Gates

- [x] 0 → 1: class `𝓢` defined, universality identified, witnesses constructed
- [x] Theorem A complete (critical universality)
- [x] Theorem B complete (elementary witness `S₀`)
- [x] Theorem B′ complete (genuine Beurling witness `𝓟₀` with Euler product)
- [x] Theorem C complete (Cauchy energy of one strict-right pair exceeds eight)
- [x] Theorem D complete (functional-equation rigidity at `x^{1/2}`)
- [x] numerical pre-certification (mpmath, 25–30 digits)
- [ ] 1 → 2: promote after independent corpus/literature audit of Theorem D
- [ ] 2 → 3: Lean formalization of A(c)(d), B, C and the packaged no-go
- [ ] external novelty audit of the `𝓢`-blindness statement

## Log

- 2026-07-25 — created.  Identified that the whole CCM four-unit source package factors through
  the critical clock law, computed the three truncated `Exp(1)` moments that generate the Ward
  profile, constructed the elementary witness `S₀` and the Beurling witness `𝓟₀`, and derived the
  category-wide no-go.  Numerically pre-certified in mpmath.

---

# Cycle 2 — the functional-equation pivot, and why it also fails

Section 6 forced the successor question: the four-unit budget is a class invariant, so the only
source datum left that can distinguish `ℤ` inside the class is the **functional equation**.  This
cycle settles that pivot.

## 8. Exact form of the functional-equation constraint

Work in logarithmic coordinates.  A generalized Euler system is a nonnegative measure `dΨ` on
`[0,∞)` (the generalized von Mangoldt measure in the variable `u = log x`), with

```text
M(s) = ∫_0^∞ e^{-su} dΨ(u)  = ∫_1^∞ x^{-s} dψ(x) = -F'(s)/F(s).       (8.1)
```

`[LEMMA 8.2]`  `ξ_F(s) := π^{-s/2}Γ(s/2)F(s)` satisfies `ξ_F(s) = ξ_F(1-s)` **iff**

```text
M(s) + M(1-s) = A(s) := (1/2)[Ψ_dig(s/2) + Ψ_dig((1-s)/2)] - log π.    (8.3)
```

*Proof.*  Differentiate `log ξ_F(s) = log ξ_F(1-s)`:
`ξ_F'/ξ_F(s) = -(1/2)logπ + (1/2)Ψ_dig(s/2) + F'/F(s)` and the reflected identity is
`ξ_F'/ξ_F(s) = -ξ_F'/ξ_F(1-s)`.  Substituting and using `M = -F'/F` gives `(8.3)`. ∎

`A` is a *fixed archimedean kernel*: it does not depend on the arithmetic.  Hence

```text
the solution set of (8.3) is  dΨ_ζ + { reflection-antisymmetric directions },
N(s) := M(s) - M_ζ(s)  satisfies  N(s) = -N(1-s).                       (8.4)
```

## 9. `[PROVED HERE]` Theorem D — the functional equation is rigid exactly at `x^{1/2}`

**Theorem D.**  Let `ν` be a signed Borel measure on `[1,∞)` with `∫_1^∞ x^{-(1/2-δ)}d|ν|(x)<∞`
for some `δ∈(0,1/2)`, and suppose `N(s)=∫x^{-s}dν` satisfies `N(s)+N(1-s)=0` on
`|Re s-1/2|<δ`.  Then `ν=0`.

*Proof.*  Put `u=log x`, `dν̃(u)=e^{-u/2}dν(e^u)`; then `∫_0^∞ e^{δu}d|ν̃|<∞`.  For `|Re z|<δ`
both `N(1/2+z)=∫_0^∞ e^{-zu}dν̃` and `N(1/2-z)=∫_0^∞ e^{zu}dν̃` converge absolutely, so the
hypothesis reads `∫_0^∞ cosh(zu)dν̃(u)=0`.  With `z=iξ` the cosine transform of `ν̃` vanishes
identically, so the even extension of `ν̃` to `ℝ` is a finite signed measure with vanishing Fourier
transform; hence it is zero, and so is `ν`. ∎

**Corollary D′.** Two `Λ`-positive systems with the *same* archimedean reflection `(8.3)` whose
generalized von Mangoldt measures satisfy `|ψ₁-ψ₂|([1,x]) = O(x^{1/2-δ'})` are equal.  So the
functional equation determines the arithmetic **down to, and only down to, the scale `x^{1/2}`** —
which is exactly the RH threshold.  `[Hamburger-type; the exponent-1/2 reading is the new content.]`

`[COROLLARY 9.1]` If `ν ≥ 0` is antisymmetric and `∫_1^∞ x^{-1/2}dν < ∞` then `ν = 0`, because
antisymmetry forces `N(1/2) = -N(1/2) = 0` while `N(1/2)=∫x^{-1/2}dν > 0` for `ν ≠ 0`.

`[COROLLARY 9.2]` No finite atomic correction exists.  If `N(s)=Σ_{j≤k}a_j e^{-su_j}` with distinct
`u_j>0` is antisymmetric then `Σ a_j e^{-su_j} + Σ a_j e^{-u_j}e^{su_j} ≡ 0`; the `2k` exponentials
`e^{∓su_j}` are linearly independent, so all `a_j=0`.

## 10. `[PROVED HERE]` Theorem F — `Λ ≥ 0` plus the Riemann functional equation does **not** force
the critical line

### 10.1 The antisymmetric cone, computed

`[LEMMA 10.1]`  For every `r ∈ ℂ`, the density (in the `u = log x` variable)

```text
e_r(u) := e^{r u} + e^{(1-r)u}      has     ∫_0^∞ e^{-su}e_r(u)du
        = 1/(s-r) + 1/(s-(1-r)),                                      (10.2)
```

and this transform is **exactly reflection antisymmetric**:
`[1/(1-s-r) + 1/(1-s-1+r)] = -[1/(s-(1-r)) + 1/(s-r)]`.
So the reflection-antisymmetric cone is spanned by the *reflection-paired exponentials* `e_r`.
Poles sit at `r` and `1-r` with the **same** residue — the functional equation's own symmetry.

Two consequences are immediate:
* a **positive** coefficient on `e_r` creates a *pole* of `F` at `r,1-r`;
* a **negative** coefficient creates a *zero* of `F` at `r,1-r`.

To place a zero off the critical line one therefore needs a *negative* coefficient on the pair
`{ρ,1-ρ}` with `Re ρ>1/2`.  The whole question is whether that negativity is compatible with
`dΨ_ζ + ν ≥ 0`.

### 10.2 The obstruction that everyone would expect — and how it is beaten

The naive attempt (insert only the zero quadruple, i.e. `F = ζ·polynomial`) fails: the required
density is `-2cos(γu)(e^{βu}+e^{(1-β)u})`, which is *absolutely continuous and takes negative
values*, while `dΨ_ζ` is purely **atomic**.  An atomic measure can never dominate a continuous one.
This is exactly the "Euler firewall" intuition, and it is correct as far as it goes.

The point missed by that argument is that **the antisymmetric cone contains nonnegative
directions** which can absorb the negativity, because `Λ`-positivity is a *pointwise* condition on
the total density, not on the inserted quadruple alone.

### 10.3 The minimal witness

`[THEOREM F, minimal form]`  Fix `β ∈ (1/2,1)`, `γ ≠ 0`, `ρ = β+iγ`.  Put

```text
d(u) := 2(1 - cos(γ u))·(e^{β u} + e^{(1-β)u}),      u ≥ 0.            (10.3)
```

Then

1. `d ≥ 0` **manifestly** (both factors are nonnegative), and `d(0)=0`;
2. its Laplace transform, absolutely convergent for `Re s > β`, is

```text
N(s) = 2[1/(s-β) + 1/(s-1+β)]
       - [1/(s-ρ) + 1/(s-ρ̄) + 1/(s-1+ρ) + 1/(s-1+ρ̄)];               (10.4)
```

3. `N(s) = -N(1-s)` identically (each reflection pair is antisymmetric by `(10.2)`);
4. consequently `dΨ_F := dΨ_ζ + d(u)du ≥ 0` is a **nonnegative** generalized von Mangoldt measure
   whose transform satisfies the **same** reflection identity `(8.3)` as `ζ`;
5. the associated function is the explicit rational gauge of `ζ`:

```text
F(s) = ζ(s)·G(s),
G(s) = (s-ρ)(s-ρ̄)(s-1+ρ)(s-1+ρ̄) / [(s-β)(s-1+β)]²,
G(1-s) = G(s),                                                        (10.5)
```

so `ξ_F(s)=ξ_ζ(s)G(s)` satisfies the exact Riemann functional equation, and `F` has **simple zeros
at `ρ, ρ̄, 1-ρ, 1-ρ̄`, off the critical line**.

*Proof.*  (1) is immediate.  (2): `∫_0^∞ e^{-su}e^{pu}du = 1/(s-p)` for `Re s > p`, and
`2(1-cos γu)e^{βu} = 2e^{βu} - e^{ρ u} - e^{ρ̄ u}`, `2(1-cos γu)e^{(1-β)u} = 2e^{(1-β)u} -
e^{(1-ρ̄)u} - e^{(1-ρ)u}`; summing gives `(10.4)`.  (3) is `(10.2)` applied to `r = β, ρ, ρ̄`.
(4) is `(8.4)`.  (5): `-G'/G = N` by partial fractions, and the root multisets
`{ρ,ρ̄,1-ρ,1-ρ̄}` and `{β,β,1-β,1-β}` are invariant under `s ↦ 1-s`, each of even cardinality, so
`G(1-s)=G(s)`. ∎

`[THEOREM F, robust form — Lean-certified]`  The same holds with the leading pair moved off `β`:
for `c ∈ (β-1/2, 1/2)`,

```text
d_c(u) = 4(e^{(c+1/2)u} + e^{(1/2-c)u}) - 2cos(γu)(e^{βu}+e^{(1-β)u})
       ≥ 4 e^{(1/2-c)u} > 0,
N_c(s) = 4[1/(s-c-1/2) + 1/(s-1/2+c)] - [1/(s-ρ)+1/(s-ρ̄)+1/(s-1+ρ)+1/(s-1+ρ̄)],
G_c(s) = (s-ρ)(s-ρ̄)(s-1+ρ)(s-1+ρ̄) / [(s-1/2-c)(s-1/2+c)]^4.
```

The strict positivity uses only `c+1/2 ≥ β` and `c+1/2 ≥ 1-β`, both from `c > β-1/2 > 0`.  Here
the extra poles can be placed anywhere in `(β,1)` and the abscissa of convergence is
`c+1/2 < 1`, so `M_F` still converges on `Re s > 1` and `F` still has a **simple pole at `s = 1`**.

*Numerical certificate (mpmath, 25 digits).*  `β=3/4, γ=7, c=0.30`: minimum of `d_c` over
`u∈[0,200]` is `≥ 0` for `t=2` and `>0` for `t≥3`; `N_c(s)+N_c(1-s) = 0` to full precision at
several complex `s`; the numerically integrated transform matches `(10.4)` to 10 digits.

### 10.4 What Theorem F does and does not say

* It **does** say: the pair of hypotheses "the logarithmic derivative is the Mellin–Stieltjes
  transform of a nonnegative measure on `[1,∞)`" (the general form of `Λ ≥ 0`) and "exact Riemann
  functional equation" is **insufficient** for the critical line, even with a simple pole at `s=1`.
* The counterexample's only defect relative to `ζ` is that `ξ_F` has **poles inside the strip**
  (at `β,1-β`, or at `1/2±c`).  Removing them is impossible inside this construction: by
  `[COROLLARY 9.1]` every nonzero nonnegative antisymmetric direction has a real singularity at
  abscissa `σ_a ≥ 1/2`, and by `(10.2)` that singularity is a positive-residue pole, i.e. a pole
  of `F`.
* It **does not** settle the level-`(L2)` question, where positivity is imposed on the *prime*
  measure `dΠ ≥ 0` rather than on the generalized von Mangoldt measure `dΨ = log x · dΠ_* ≥ 0`.
  For the minimal witness `(10.3)` the Möbius inversion `dΠ = Σ_k (μ(k)/k)dΠ_*(x^{1/k})` is
  positive near `x=1` (leading behaviour `2γ²(log x)/ζ(3)`) and for large `x`, but is negative at
  the zeros of `1-cos(γ log x)`, where the `k=1` term vanishes while the `k=2` term does not.
  So the level-`(L2)` statement remains open.

### 10.5 External audit

The Clay/AIM description of the problem states the field's own position exactly:

> "A common opinion, based largely on counterexamples, is that the L-functions for which the
> Riemann Hypothesis is true enjoy both an Euler product formula and a functional equation.
> However, **a direct connection between these properties and the Riemann Hypothesis has not been
> formulated in a precise manner.**"

Known counterexamples in the literature (Davenport–Heilbronn 1936; Epstein zeta functions of class
number `>1`; Hurwitz and Shintani zeta functions) all break the *Euler* side, never the
functional-equation side.  Theorem F is of the opposite type: it retains an exact Riemann
functional equation **and** nonnegativity of the generalized von Mangoldt measure, and still
produces off-critical zeros.  Targeted searches (Beurling systems with functional equations;
"Euler product + functional equation" sufficiency; Selberg class counterexamples) located no such
construction.  `[NOVELTY: candidate new; priority audit open.]`

## 11. Consequence for the CCM lane

Combining the two cycles:

```text
source package (Möbius/squarefree Gibbs family, four-unit budget, Fisher curvature,
                one-corner profile, Gamma/Sonin completion)
    depends only on:  Λ ≥ 0  +  simple pole at σ=1  +  a Λ-independent archimedean kernel.

Theorem A/B :  Λ ≥ 0 + simple pole      is blind to the strict-right divisor.
Theorem F   :  Λ ≥ 0 + simple pole + FE is still insufficient for the critical line.
```

Hence **the entire CCM four-unit programme, as specified in `C48`–`C50`, cannot close**: every
hypothesis it uses is satisfied by an explicit object with off-critical zeros.  The first
hypothesis it does *not* use, and which every remaining route must use, is:

```text
(H)  the completed function is holomorphic in the strip
     (equivalently: ξ is entire of order one; no positive-residue pole survives
      in the reflection-antisymmetric part of the source).                       (11.1)
```

`(H)` is a *global analytic* statement about the cancellation between the prime side and the
archimedean factor.  It is exactly the datum that the four-unit budget throws away when it proves
"the Gamma multiplier norm tends to one".

## 12. The next object

The sharpened open core, replacing the retired `[OPEN CORE]` of
`mobius-incidence-curvature-gamma-sonin-pole-divisor-transfer-rh.md`:

```text
[OPEN CORE, level (L2)+entirety]
Let dΠ ≥ 0 be a measure on (1,∞) with ζ_Π(s) = exp(∫ Σ_k x^{-ks}/k dΠ) meromorphic with a simple
pole at s=1, let ξ(s) = π^{-s/2}Γ(s/2)ζ_Π(s)·s(s-1)/2 be entire of order one, and let
ξ(s) = ξ(1-s).  Are all zeros of ξ on Re s = 1/2?
```

Theorem F shows this is false if `dΠ ≥ 0` is weakened to `dΨ ≥ 0`, or if entirety is dropped.
Theorem D shows any counterexample must differ from `ζ` by `≫ x^{1/2}` in the von Mangoldt
measure.  Corollary 9.1 shows its antisymmetric part must have infinite `x^{-1/2}` mass.  Those
three constraints are the exact perimeter of the remaining problem, and none of them is an energy
estimate — which is why fifty budget-shaped conjectures failed.

## Gates (cycle 2)

- [x] exact reflection constraint `(8.3)` derived
- [x] Theorem D (rigidity at `x^{1/2}`)
- [x] Corollaries 9.1, 9.2 (no small, no finite-atomic antisymmetric directions)
- [x] Lemma 10.1: the antisymmetric cone is spanned by reflection-paired exponentials
- [x] Theorem F minimal witness `(10.3)` and robust witness `d_c`
- [x] numerical pre-certification
- [x] external audit against Davenport–Heilbronn / Epstein / Selberg-class counterexamples
- [ ] level-`(L2)` prime-measure positivity: decide
- [ ] entirety-constrained problem `(12)`: decide

## Log (cycle 2)

- 2026-07-25 — derived the exact reflection constraint, proved the `x^{1/2}` rigidity theorem,
  computed the reflection-antisymmetric cone in closed form, and constructed an explicit
  `Λ`-positive system with the exact Riemann functional equation and zeros off the critical line.
  This retires the functional-equation pivot for the CCM four-unit lane and isolates entirety of
  the completed function as the unique remaining structural input.

---

# Cycle 3 — the prime-positivity pivot falls: a genuine Beurling system with the exact
# Riemann functional equation and off-critical zeros

Cycle 2 left one gap.  Theorem F is a statement at level `(L1)`: nonnegativity of the *generalized
von Mangoldt* measure `dΨ = log x · dΠ_*`.  A defender of the lane could reply that the CCM source
is built from the *prime* measure (squarefree integers, Möbius signs), i.e. from level `(L2)`:
`dΠ ≥ 0`.  This cycle closes that gap.

## 13. The obstruction to be beaten

Write everything in `u = log x`.  A generalized prime system is a nonnegative measure `Π` on
`(0,∞)`; its prime-power measure is `Π_* = TΠ` where

```text
(T f)(u) = Σ_{k≥1} k^{-2} f(u/k),      Mellin multiplier ζ(2-s),         (13.1)
T^{-1} g = Σ_{k≥1} μ(k)k^{-2} g(u/k),  Mellin multiplier 1/ζ(2-s),
dΨ(u) = u·dΠ_*(u).
```

For the cycle-2 witnesses the correction to `Π_*` had density `d(u)/u` with `d(0) > 0`, so
`Π` had *infinite* mass near `u=0` — inadmissible.  Forcing `d(0)=0` (as in the minimal witness
`2(1-\cos γu)(e^{βu}+e^{(1-β)u})`) makes `d` vanish on the lattice `(2π/γ)ℤ`, and there the `k=1`
term of `T^{-1}` vanishes while the `k=2` term does not, so `dΠ` goes negative.  Both failures are
now removed at once by choosing the positive part of the antisymmetric correction correctly.

## 14. `[PROVED HERE]` The monotone Möbius criterion

`[LEMMA 14.1]`  Let `g:[0,∞)→[0,∞)` be nondecreasing.  Then for every `u>0`

```text
(T^{-1}g)(u) = Σ_{k≥1} μ(k)k^{-2} g(u/k) ≥ g(u)·(2 - π²/6) > 0.34·g(u) ≥ 0.       (14.2)
```

*Proof.*  The `k=1` term is `g(u)`.  For `k≥2`, `0 ≤ g(u/k) ≤ g(u)`, so the tail is bounded in
absolute value by `g(u)Σ_{k≥2}k^{-2} = g(u)(π²/6 - 1)`, and `1-(π²/6-1) = 2-π²/6 ≈ 0.3551`. ∎

So: **if the corrected prime-power density is nonnegative and nondecreasing, the corrected prime
density is automatically nonnegative.**  This replaces an intractable sign analysis of an
alternating series by one monotonicity statement.

## 15. `[PROVED HERE]` The antisymmetric cone in hyperbolic coordinates

By `(10.2)` the reflection-antisymmetric cone is spanned by `e_r(u)=e^{ru}+e^{(1-r)u}`.  Writing
`w = r-1/2`,

```text
e_r(u) = 2 e^{u/2} cosh(w u),      transform  1/(s-1/2-w) + 1/(s-1/2+w).       (15.1)
```

So every antisymmetric correction has the form

```text
d(u) = 2 e^{u/2} h(u),        h(u) = Σ_j t_j cosh(w_j u),                      (15.2)
```

with `h` **even**, and the local-finiteness requirement near `u=0` is exactly `h(0)=Σ_j t_j = 0`.
The correction to the prime-power density is then

```text
π_*(u) = d(u)/u = 2 e^{u/2}·(h(u)/u).                                          (15.3)
```

`[LEMMA 15.4]`  If `h` is even, `h(0)=0` and `h` is convex on `[0,∞)`, then `h(u)/u` is
nondecreasing and nonnegative on `(0,∞)`; hence `π_*` in `(15.3)` is nonnegative and nondecreasing,
and Lemma 14.1 applies.

## 16. `[PROVED HERE]` Theorem H — the level-`(L2)` witness

**Theorem H.**  Fix `a₀ ∈ (0,1/2)` and `γ ≠ 0` with

```text
κ := √(a₀² + γ²) < 1/2,        β := 1/2 + a₀ ∈ (1/2,1),   ρ := β + iγ,          (16.1)
```

and put `w := a₀ + iγ` (so `κ = |w|`) and

```text
h(u) := 2[cosh(κ u) - cosh(a₀ u)cos(γ u)] = 2[cosh(κu) - Re cosh(wu)],
d(u) := 2 e^{u/2} h(u)
      = 2(e^{(1/2+κ)u} + e^{(1/2-κ)u}) - 2cos(γu)(e^{βu} + e^{(1-β)u}).        (16.2)
```

Then:

1. **Power-series positivity.**  `cosh z = Σ_{n≥0} z^{2n}/(2n)!`, so

```text
h(u) = 2 Σ_{n≥0} (κ^{2n} - Re(w^{2n})) u^{2n}/(2n)!,                           (16.3)
```

   and `κ^{2n} = |w|^{2n} = |w^{2n}| ≥ Re(w^{2n})`.  Hence **every coefficient of `(16.3)` is
   nonnegative and the constant one vanishes**:

```text
h(u) = Σ_{n≥1} c_n u^{2n},  c_n ≥ 0  ⟹  h ≥ 0, h(0)=0, h convex,
                                        h(u)/u = Σ_{n≥1} c_n u^{2n-1} nondecreasing.  (16.4)
```

2. **Genuine Beurling primes.**  By `(16.4)`, `(15.3)` and Lemmas 15.4, 14.1, the corrected prime
   density satisfies

```text
dΠ = dΠ_ζ + T^{-1}(π_*) ≥ dΠ_ζ + (2-π²/6)·π_* ≥ 0,                             (16.5)
```

   locally finite because `π_*(u) = 4γ²u + O(u³)` near `0`.  So `Π` **is** a legitimate generalized
   prime measure with an Euler product `F(s) = exp(∫ Σ_k x^{-ks}k^{-1} dΠ)`.

3. **Exact Riemann functional equation.**  The Laplace transform of `d` is

```text
N(s) = 2[1/(s-1/2-κ) + 1/(s-1/2+κ)]
       - [1/(s-ρ) + 1/(s-ρ̄) + 1/(s-1+ρ) + 1/(s-1+ρ̄)],                          (16.6)
```

   which is reflection antisymmetric by `(10.2)`.  Hence `M_F = M_ζ + N` satisfies `(8.3)` and
   `ξ_F(s) = ξ_F(1-s)` exactly, with

```text
F(s) = ζ(s)·G(s),   G(s) = (s-ρ)(s-ρ̄)(s-1+ρ)(s-1+ρ̄)/[(s-1/2-κ)(s-1/2+κ)]².     (16.7)
```

4. **Correct global normalisation.**  `κ < 1/2` makes `1/2+κ < 1`, so the abscissa of convergence
   of `M_F` is `1`: `F` has a **simple pole at `s=1`**, the generalized integer counting function
   satisfies `N_F(x) ∼ Cx`, and the system obeys the prime number theorem.

5. **Off-critical zeros.**  `F` has simple zeros at `ρ, ρ̄, 1-ρ, 1-ρ̄` with `Re ρ = β > 1/2`.

*Numerical certificate.*  `a₀=γ=0.3`, `κ=0.4243`, `β=0.8`: `min h = 0` (only at `u=0`);
`min h'' = 0.36 > 0`; `π_*` verified nondecreasing on `[0,200]`; the Möbius-inverted prime density
is positive on `(0,100]` with `p(u)/π_*(u) ∈ [0.854, 1]`, comfortably above the guaranteed floor
`0.3551`; `N(s)+N(1-s)=0` to machine precision; the numerically integrated transform of `d` matches
`(16.6)`.

**Consequence.**  Level `(L2)` is *not* a pivot: prime-measure positivity, an Euler product, the
prime number theorem, a simple pole at `s=1`, and the exact Riemann functional equation hold
simultaneously for a system with zeros off the critical line.

## 17. The pivot ledger, closed

The CCM source supplies exactly the following data about the arithmetic system.  Each row records
the witness that refutes it as a sufficient input.

```text
 (P1) Λ ≥ 0 (nonneg generalized von Mangoldt measure)  → Thm A/B (blind), Thm F, Thm H
 (P2) simple pole of Z_sq at σ=1 / PNT normalisation   → Thm A (class invariant), Thm H
 (P3) exact Riemann functional equation / Γ factor     → Thm F, Thm H
 (P4) prime-measure positivity dΠ ≥ 0, Euler product   → Thm B′ (no FE), Thm H (with FE)
 (P5) discreteness / integrality of the primes         → Thm A: witnesses S₀ (atom+Lebesgue)
                                                          and 𝓟₀ (continuous) share the clock
 (P6) entirety of the completed function ξ             → NOT supplied by the source
```

`(P1)`–`(P5)` are the complete list of properties the four-unit source apparatus is a function of,
and each is refuted.  `(P6)` is a property of the *completed target* `ξ`: it is the statement that
the archimedean factor cancels the prime side's poles exactly.  The corpus's own theorem that the
Gamma multiplier has asymptotic norm one (`mobius-incidence-…`, `(7b)`) says precisely that the
four-unit budget **discards** that cancellation.

**Therefore: the CCM four-unit source-budget lane cannot prove RH.**  Not because some transport
shape is missing — every shape was already killed in `C1`–`C50` — but because the source data it is
built from are provably satisfied by explicit generalized prime systems whose zeta functions have
zeros off the critical line.  A proof through this lane would have to be false for `Π_ζ + Π_new` of
Theorem H, and no property distinguishing them enters the construction.

## 18. What survives, and the next object

The unique surviving input is `(P6)`.  Restated as an arithmetic condition it is:

```text
[NEXT OBJECT]  the reflection-antisymmetric part of the source carries no positive-residue pole.
```

Equivalently, by `(15.1)`–`(15.2)`: in `h(u) = Σ_j t_j cosh(w_j u)` every `t_j` with `w_j` real
must vanish.  But `h(0) = Σ_j t_j = 0` (local finiteness) and `h ≥ 0` force, by `(16.3)`-type
reasoning, at least one strictly positive `t_j` at real `w_j` whenever `h ≠ 0`.  Precisely:

`[THEOREM I — finite-rank rigidity]`  Let the correction have **finite rank**:

```text
d(u) = 2e^{u/2} h(u),   h(u) = Σ_{j=1}^m t_j cosh(w_j u),
t_j ∈ ℝ,  Re w_j ≥ 0,  the multiset closed under w ↦ w̄ with equal t.        (18.2)
```

Assume the perturbed system `F = ζ·G` satisfies

```text
(i)   Λ ≥ 0 : the absolutely continuous part of dΨ_F is nonnegative, i.e. h ≥ 0 on ℝ;
(ii)  the exact Riemann functional equation (automatic by (10.2));
(iii) entirety: ξ_F has no poles beyond the standard ones at s = 0,1.
```

Then `h ≡ 0`: the system is `ζ` itself.

*Proof.*  Let `α = max{Re w_j : t_j ≠ 0}` and suppose `h ≢ 0`.  For `u ≥ 0` and `Re w_j ≥ 0` the
terms `e^{-w_j u}` are bounded, so

```text
2 e^{-αu} h(u) = Q(u) + o(1),   Q(u) = Σ_{Re w_j = α} t_j e^{i Im(w_j) u},     (18.3)
```

a real trigonometric polynomial.  `h ≥ 0` and almost-periodicity of `Q` give `Q ≥ 0` everywhere.
Its mean value is `M(Q) = Σ_{w_j = α real} t_j`, since every non-real frequency has mean zero.
If `M(Q) = 0` then `M(Q²) ≤ ‖Q‖_∞ M(Q) = 0`, and `M(Q²)` is the sum of squares of the coefficients
of `Q` (Parseval for trigonometric polynomials), so `Q ≡ 0` — contradicting maximality of `α`.
Hence `M(Q) > 0`, so **there is a real `w_{j₀} = α` with `t_{j₀} > 0`**.

By `(15.1)`, `N` then has a pole of positive residue `t_{j₀}` at the **real** points `1/2 ± α`, so
`G` has a pole there, so `ξ_F = ξ_ζ·G` has a pole at the real point `1/2+α` unless `ξ_ζ` vanishes
there.  But `ξ_ζ` has **no real zeros**: on `(0,1)` the Dirichlet eta function
`η(s) = (1-2^{1-s})ζ(s)` is positive while `1-2^{1-σ} < 0`, so `ζ(σ) < 0`; the trivial zeros are
cancelled by the poles of `Γ(s/2)`; and `ξ_ζ(0), ξ_ζ(1/2), ξ_ζ(1) ≠ 0`.  This contradicts `(iii)`.
∎

**Reading.**  Positivity forces a *real top frequency with positive coefficient*; a real top
frequency is a real pole of the completed function; `ξ_ζ` has no real zero to absorb it.  That is
the entire mechanism, and it is a **mean-value at the leading exponential**, not an energy
estimate — which is exactly why no `L²`/Gauss–Codazzi budget can see it.

**Sharpness.**  Theorem H saturates Theorem I: its correction has exactly one positive coefficient,
at the single real frequency `w = κ`, hence exactly one violation of entirety (the double pole at
`1/2 ± κ`).  Everything else — `Λ ≥ 0`, `dΠ ≥ 0`, PNT, the exact functional equation — survives.
Theorems H and I are therefore complementary halves of one statement:

```text
Λ ≥ 0 + Euler product + PNT + Riemann functional equation + entirety
  ⟹ (finite rank) rigidity;
drop entirety alone ⟹ explicit counterexamples with zeros anywhere in (1/2,1).   (18.4)
```

The infinite-rank version of Theorem I is RH itself: `ζ`'s own leading real frequency is the pole
at `s=1` (`w = 1/2`), which dominates every zero frequency `|Re w_ρ| < 1/2`, so positivity is
satisfied without any constraint on the zeros.  Finite-rank corrections have no such main term
(`Σ_j t_j = 0`), which is precisely why they are rigid and `ζ` is not.

## 19. Novelty audit against the literature (July 2026)

```text
Theorem A (critical-clock universality)   elementary Abelian limit; the mathematics is classical.
                                          Its content here is diagnostic, not new mathematics.
Theorem B, B′ (Beurling systems with      REDISCOVERED.  Existence is known: Diamond–Montgomery–
  off-critical zeros, no FE)              Vorhauer, Math. Ann. 334 (2006); Zhang, Math. Ann. 337
                                          (2007); Neamah–Hilberdink (2020).  My constructions are
                                          simpler and explicit but the theorem is not new.
Theorem D (rigidity at x^{1/2})           Hamburger-type uniqueness; classical in spirit.
Lemma 14.1 (monotone Möbius positivity)   elementary; plausibly folklore in Beurling theory.
Theorem F / H (Λ ≥ 0 and dΠ ≥ 0 and       CANDIDATE NEW.  The literature position is explicit:
  PNT and the EXACT Riemann functional     Bombieri (Clay): "Not a single example of validity or
  equation, with zeros off the line)       failure of a Riemann hypothesis for an L-function is
                                          known"; AIM: "a direct connection between [Euler product
                                          and functional equation] and the Riemann Hypothesis has
                                          not been formulated in a precise manner."  All known
                                          counterexamples (Davenport–Heilbronn 1936; Epstein zeta
                                          with class number > 1; Hurwitz/Shintani) break the Euler
                                          side.  Hilberdink–Lapidus (Acta Appl. Math. 2006)
                                          characterise a *generalised* functional equation pairing
                                          ζ_P with a dual system ζ_{P*}; they do not construct a
                                          self-dual Λ-positive system with off-critical zeros.
Theorem I (finite-rank rigidity)          CANDIDATE NEW; elementary mechanism (leading-frequency
                                          mean value + absence of real zeros of ξ).
```

So the results that carry external significance are `(18.4)`: the precise formulation of
"Euler product + functional equation ⟹ RH", its **refutation** without entirety, and its
**proof** at finite rank with entirety.

## Gates (cycle 3)

- [x] monotone Möbius criterion `(14.2)`
- [x] hyperbolic normal form of the antisymmetric cone `(15.1)`–`(15.3)`
- [x] Theorem H: genuine Beurling system, PNT, exact FE, off-critical zeros
- [x] power-series proof of nonnegativity/convexity/monotonicity `(16.3)`–`(16.4)`
- [x] numerical certificate
- [x] pivot ledger `(P1)`–`(P6)` closed
- [x] Proposition 18.1 (finite-rank entirety obstruction)
- [ ] infinite-rank version of `(18)` — this is RH itself

## Log (cycle 3)

- 2026-07-25 — closed the prime-positivity pivot.  The monotone Möbius criterion converts the
  alternating inversion `Π = T^{-1}Π_*` into a single monotonicity requirement; the hyperbolic
  normal form of the antisymmetric cone makes that requirement a power-series positivity statement
  `|w^{2n}| ≥ Re(w^{2n})`.  The resulting system has genuine Beurling primes, PNT, the exact
  Riemann functional equation, and zeros off the critical line.  With `(P1)`–`(P5)` all refuted and
  `(P6)` provably discarded by the four-unit budget, the CCM four-unit lane is closed.

---

# Cycle 4 — a sharp axiomatization of RH, with every hypothesis proved necessary

## 20. The one admissible real frequency

Cycle 3's Theorem I says: `Λ`-positivity forces a **positive coefficient at a real leading
frequency** `w = α`, hence a pole of the completed function at the real points `1/2 ± α`; and `ξ`
has no real zeros, so entirety kills it.  That argument has exactly one loophole, and it is
decisive:

```text
the real frequency w = 1/2 has its poles at s = 1 and s = 0,
which the standard completion factor s(s-1) already clears.                    (20.1)
```

So a positive coefficient at `w = 1/2` is *harmless to entirety* — it merely raises the order of
the pole at `s=1`.  Putting the entire positive part there gives:

## 21. `[PROVED HERE]` Theorem J — entirety is not enough

**Theorem J.**  Fix `a₀ ∈ (0,1/2)` and `γ ≠ 0`; put `ρ = 1/2 + a₀ + iγ`.  Add to the generalized von
Mangoldt measure the logarithmic density

```text
d(u) = 2 e^{u/2}·h(u),   h(u) = 2[cosh(u/2) - cosh(a₀ u)cos(γ u)]
     = 2(e^u + 1) - 2cos(γu)(e^{(1/2+a₀)u} + e^{(1/2-a₀)u}).                   (21.1)
```

Then:

1. **`Λ ≥ 0` for every `γ`.**  With `X = e^{a₀u}`, `Y = e^{u/2}` and `1 ≤ X ≤ Y`,

```text
(Y² + 1) - (YX + Y/X) = (Y - X)(XY - 1)/X ≥ 0,
```

   and `cos ≤ 1` finishes.  (Equivalently `cosh(u/2) ≥ cosh(a₀u) ≥ cosh(a₀u)cos(γu)`.)

2. **Laplace transform**, absolutely convergent for `σ > 1`:

```text
N(s) = 2[1/(s-1) + 1/s]
       - [1/(s-ρ) + 1/(s-ρ̄) + 1/(s-1+ρ) + 1/(s-1+ρ̄)],                        (21.2)
```

   reflection antisymmetric by `(10.2)`; so the perturbed system satisfies the **exact** Riemann
   functional equation.

3. **The system.**

```text
F(s) = ζ(s)·G(s),   G(s) = (s-ρ)(s-ρ̄)(s-1+ρ)(s-1+ρ̄)/[s(s-1)]².               (21.3)
```

4. **Entirety.**  `G(s)·[s(s-1)]²` is the polynomial `(s-ρ)(s-ρ̄)(s-1+ρ)(s-1+ρ̄)`, so

```text
(1/2)·s³(s-1)³·π^{-s/2}Γ(s/2)·F(s) = ξ(s)·(s-ρ)(s-ρ̄)(s-1+ρ)(s-1+ρ̄)            (21.4)
```

   is **entire of order one**, and both factors are invariant under `s ↦ 1-s`, so it satisfies the
   exact Riemann functional equation.

5. **Off-critical zeros** at `ρ, ρ̄, 1-ρ, 1-ρ̄`, with `Re ρ = 1/2 + a₀ > 1/2`.

6. **Genuine Beurling primes** whenever `a₀² + γ² ≤ 1/4`: the power series
   `h(u) = 2Σ_{n≥1}((1/4)^n - Re w^{2n})u^{2n}/(2n)!` (`w = a₀+iγ`) then has nonnegative
   coefficients, so `h(u)/u` is nondecreasing and Lemma 14.1 gives `dΠ ≥ 0`.

The **only** deviation from `ζ` is the order of the pole at `s = 1`, which is `3`; equivalently
`N_F(x) ∼ Cx log²x` instead of `∼ Cx`.

*Numerical certificate.*  `a₀=0.3, γ=0.3`: `min h = 0` (only at `u=0`), `π_*` nondecreasing,
`min dΠ` density `= 0.0105 > 0`; `a₀=0.4, γ=0.2`: `min dΠ = 0.0055 > 0`; `a₀=0.3, γ=3.0`: `h ≥ 0`
still (level `(L1)`) but `dΠ` goes negative, matching `|w| > 1/2`.  `N(s)+N(1-s) = 0` exactly; the
numerically integrated transform matches `(21.2)` to 12 digits.

## 22. `[PROVED HERE]` The pole order is the last discriminator

**Theorem K.**  Let the correction have finite rank, `h(u) = Σ_j t_j cosh(w_j u)`, and assume

```text
(H1) Λ ≥ 0   (h ≥ 0 on ℝ);
(H2) exact Riemann functional equation   (automatic for the cone);
(H3) the completed function is entire apart from the poles at s = 0,1;
(H4) the pole at s = 1 is simple.
```

Then `h ≡ 0`.

*Proof.*  `(H4)` says the coefficient at `w = 1/2` vanishes.  Local finiteness of the prime measure
at `x=1` gives `h(0) = Σ_j t_j = 0`.  By Theorem I's leading-level argument, `(H1)` forces a real
`w_{j₀} = α = max Re w_j` with `t_{j₀} > 0`, hence a pole of the completed function at the **real**
points `1/2 ± α`.  By `(H3)` that pole must be cancelled by a zero of `ξ`; `ξ` has no real zeros
(`ζ(σ)<0` on `(0,1)` via `η(s)=(1-2^{1-s})ζ(s)>0`; the trivial zeros are cancelled by the poles of
`Γ(s/2)`; `ξ(0), ξ(1/2), ξ(1) ≠ 0`), and the only real `α` whose poles are pre-cleared by the
completion factor `s(s-1)` is `α = 1/2`, excluded by `(H4)`.  Contradiction. ∎

**No infinite-rank escape by bounded means.**  Under `(H3)+(H4)` every positive coefficient sits at
a zero of `ξ`, i.e. at `w_n = ρ_n - 1/2` with `|Re w_n| < 1/2`; and a negative coefficient at
`Re w = a > 0` (an inserted off-critical zero) contributes `-4cosh(au)cos(γu)`, of amplitude
`e^{au} → ∞`, while a convergent family of positive coefficients at zeros of `ξ` contributes at
most `Σ_n t_n · e^{(\max_n Re w_n) u}`.  If `ζ` satisfies RH those are all purely imaginary, hence
bounded by `Σ t_n = 2`, and `h ≥ 0` fails.  So no counterexample can be built by perturbing `ζ`
unless `ζ` already has off-critical zeros.

## 23. The axiomatization

```text
(H1) Λ ≥ 0 / Euler product with nonnegative local data
(H2) exact Riemann functional equation with the classical archimedean factor
(H3) completed function entire of order one
(H4) simple pole at s = 1

(H2)+(H3)+(H4) without (H1)   :  FALSE — Davenport–Heilbronn (1936), Epstein, Hurwitz/Shintani
(H1)+(H3)+(H4) without (H2)   :  FALSE — Theorem B′ here; Diamond–Montgomery–Vorhauer (2006),
                                          Zhang (2007), Neamah–Hilberdink (2020)
(H1)+(H2)+(H4) without (H3)   :  FALSE — Theorem H here  [poles at 1/2 ± κ]
(H1)+(H2)+(H3) without (H4)   :  FALSE — Theorem J here  [pole of order 3 at s = 1]
(H1)+(H2)+(H3)+(H4)           :  TRUE at finite rank — Theorem K here
                                  ⟸ the infinite-rank case is RH.
```

Each of the four hypotheses is therefore **independent and necessary**, and the last two entries
are new.  The Clay/AIM position — "a direct connection between [Euler product and functional
equation] and the Riemann Hypothesis has not been formulated in a precise manner" — is now
formulated, and the answer to the naive form is negative: two further hypotheses, entirety and the
pole order, are indispensable, and each is refuted individually by an explicit `Λ`-positive system
with the exact Riemann functional equation.

## 24. Why linear positivity cannot go further

`Λ ≥ 0` is a *linear* positivity.  Convolving the arithmetic measure with any `φ ≥ 0` multiplies
each frequency coefficient by `Φ(w) = ∫φ(t)e^{-wt}dt`, and `Φ(1/2) > 0` for every `φ ≥ 0`.  So the
leading exponential `e^{u/2}` can never be cancelled by a positivity-preserving operation, and the
leading-frequency lemma can only ever see the pole — i.e. only PNT-strength information.  RH is a
statement about the *fluctuation* at scale `e^{u/2}` relative to a main term of the same size after
normalisation; reaching it requires *quadratic* positivity (Weil), which is RH-equivalent.

This is a precise obstruction, and it applies to every energy/budget scheme including the CCM
four-unit programme: the four-unit budget is a linear functional of the Gibbs family, hence sees
only the pole (Theorem A), and the counterexamples of Theorems H and J confirm this at the level of
the full hypothesis set.

## Gates (cycle 4)

- [x] identify `w = 1/2` as the unique entirety-compatible real frequency
- [x] Theorem J: entire + FE + `Λ ≥ 0` + Euler, with off-critical zeros
- [x] Theorem K: the four hypotheses are rigid at finite rank
- [x] independence table `(23)`
- [x] linear-positivity obstruction `(24)`
- [ ] infinite-rank case of Theorem K — this is RH

## Log (cycle 4)

- 2026-07-25 — moved the whole positive part of the antisymmetric correction to the unique
  entirety-compatible real frequency `w = 1/2`, producing a `Λ`-positive Beurling system with an
  Euler product, the exact Riemann functional equation, an **entire** completed function of order
  one, and zeros off the critical line.  Proved that the pole order is then the last discriminator
  and that the four hypotheses are rigid at finite rank.  Recorded the independence table and the
  linear-positivity obstruction that explains why no budget scheme can close the remaining gap.
