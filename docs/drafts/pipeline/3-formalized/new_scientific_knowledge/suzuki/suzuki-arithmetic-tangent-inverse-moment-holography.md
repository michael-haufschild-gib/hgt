# Suzuki arithmetic tangent and inverse-moment holography

- **ID:** `suzuki-arithmetic-tangent-inverse-moment-holography`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / RESTRICTED-WEIL SOURCE RESPONSE / SPECTRAL RECONSTRUCTION
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED]`
  `[GENERIC PERTURBATION AND MOMENT DETERMINACY CLASSICAL] [NOT AN RH PROOF]`
- **Primary source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1 (2026), Theorem 1.5 and Sections 6--8.

## 1. Exact setup

Fix `a>0` and an admissible shift `lambda<lambda_a`.  Let `nu` be the spectral probability of the
normalized positive deficiency vector for Suzuki's canonical even extension, as identified in
`suzuki-donoghue-defect-spectral-measure-law.md`.  Its Donoghue function is

```text
R_nu(z) = integral_R 1/(t-z) dnu(t),
m_nu(z) = z + (z^2+1) R_nu(z).                            (1)
```

The measure is even, pure atomic, and has no atom at zero.  At fixed aperture its support is closed
and discrete, hence is separated from zero.  Define its inverse even moments

```text
q_n(nu) = integral_R t^(-2n) dnu(t),       q_0=1.          (2)
```

All moments in `(2)` are finite because the support has a positive gap about zero.

For the far-negative shift chart, write `lambda=-r`, `epsilon=1/r`, and

```text
f_+(x)=e^x,
u_epsilon=(I+epsilon A_a)^(-1)f_+,
F_epsilon(z)=integral_(-a)^a u_epsilon(x)e^(izx) dx.       (3)
```

The scalar factor `epsilon` in `(A_a+rI)^(-1)=epsilon(I+epsilon A_a)^(-1)` cancels from Suzuki's
projective quotient.  Put

```text
F_0(z)=integral_(-a)^a e^x e^(izx) dx,
H_a(z)=integral_(-a)^a (A_a e^x)(x)e^(izx) dx,
h_a(z)=H_a(z)/F_0(z),
Delta_a(z)=h_a(-z)-h_a(z).                                (4)
```

Thus `Delta_a` is the anti-reflected normalized restricted-Weil matrix coefficient.  It vanishes
for a scalar operator and therefore removes exactly the projectively invisible common scale.

## 2. Theorem A: complete inverse-moment holography

For every `n>=0`,

```text
m_nu^(2n+1)(0)/(2n+1)! = q_n(nu)+q_(n+1)(nu).             (5)
```

Consequently the complete odd Taylor jet of `m_nu` at zero recovers all inverse moments by

```text
q_0=1,
q_(n+1)=m_nu^(2n+1)(0)/(2n+1)!-q_n.                       (6)
```

This moment sequence determines the entire even measure `nu`, not merely a finite spectral prefix.
Indeed, push `nu` forward by `t |-> t^(-2)`.  The resulting probability `rho_nu` is supported on the
compact interval `[0,delta^(-2)]`, where `delta=dist(0,supp nu)>0`, and

```text
integral y^n drho_nu(y)=q_n(nu).                           (7)
```

Compact moment determinacy gives `rho_nu` uniquely.  Evenness then recovers `nu`: each positive
radius receives half its mass at each sign.

The scale-free sequence

```text
kappa_n(nu)=q_n(nu)/q_1(nu)^n                              (8)
```

is invariant under every spectral dilation `t |-> c t`, `c>0`, because
`q_n |-> c^(-2n)q_n`.  Conversely, the complete sequence `(kappa_n)` determines the even zero-free
probability up to dilation.  It is the moment sequence of the canonical normalized observable

```text
Y_nu(t)=1/(q_1(nu)t^2),        integral Y_nu dnu=1.        (9)
```

Thus `(8)` is a complete projective spectral coordinate, not another finite Schur prefix.

The first two recovered quantities are

```text
q_1=m_nu'(0)-1,
q_2=m_nu'''(0)/6-q_1.                                    (10)
```

For Suzuki's source presentation `m=-i W_1/W_(-1)` with Fourier transform `F`, direct
differentiation at zero gives the especially small source observable

```text
q_1=-i F'(0)/F(0).                                        (11)
```

For the exact free clock `m_a^free(z)=coth(a)tan(az)`,

```text
q_1^free=a coth(a)-1,
q_2^free=(a^3/3)coth(a)-a coth(a)+1.                      (12)
```

Equality with a dilation of the free clock is therefore equivalent to equality of every
`kappa_n`; one unequal `kappa_n` is an exact non-clock certificate.

## 3. Proof of Theorem A

At a regular point, differentiation under the Cauchy transform gives

```text
R_nu^(j)(0)=j! integral_R t^(-j-1) dnu(t).                (13)
```

Set `r=2n+1`.  For `n>=1`, Leibniz's rule applied to `(1+z^2)R_nu(z)` leaves only the zeroth and
second derivatives of `1+z^2` at zero:

```text
m_nu^(r)(0)
 =R_nu^(r)(0)+r(r-1)R_nu^(r-2)(0)
 =r!q_(n+1)+r(r-1)(r-2)!q_n
 =r!(q_n+q_(n+1)).                                        (14)
```

For `n=0`, the derivative of the leading `z` supplies `q_0=1`, giving the same formula.  This proves
`(5)--(6)`.  Equations `(7)--(9)` follow from compact moment determinacy and change of variables.
Equations `(10)--(12)` are direct substitutions into `(5)`.

## 4. Theorem B: first arithmetic tangent away from the free clock

The operator `A_a` is unbounded, so no operator-norm Neumann expansion is available.  The source
domain theorem in `suzuki-boundary-log-nonclock-nonflat-tangent.md` proves
`e^x in Dom(A_a)`.  Therefore, as `epsilon -> 0+`, the resolvent has the strong source-vector
expansion

```text
(I+epsilon A_a)^(-1)e^x=e^x-epsilon A_a e^x+o(epsilon) in L^2.
```

Consequently, locally uniformly in `z`,

```text
F_epsilon(z)=F_0(z)-epsilon H_a(z)+o(epsilon).             (15)
```

Let

```text
Theta_epsilon(z)
 =(z-i)F_epsilon(z)/((z+i)F_epsilon(-z)),
m_epsilon(z)=i(1+Theta_epsilon(z))/(1-Theta_epsilon(z)).   (16)
```

Away from the displayed denominators and the free clock poles, the exact first variations are

```text
dot Theta_a(z)=Theta_a^free(z) Delta_a(z),                (17)

dot m_a(z)
 =2i Theta_a^free(z) Delta_a(z)/(1-Theta_a^free(z))^2.    (18)
```

In particular the first inverse-moment response is

```text
dot q_1(a)=dot m_a'(0)=i h_a'(0).                         (19)
```

Writing

```text
U_0=integral e^x dx,        M_1=integral x e^x dx,
U_A=integral A_a(e^x) dx,  M_(1,A)=integral x A_a(e^x) dx,
```

and using `q_1^free=M_1/U_0=a coth(a)-1`, equation `(19)` becomes the source-only law

```text
dot q_1(a)
 =-(M_(1,A)U_0-U_A M_1)/U_0^2
 =-(M_(1,A)-q_1^free U_A)/U_0.                            (20)
```

This is the centered restricted-Weil matrix coefficient which first bends the universal clock.
No arbitrary normalization remains.

There is also an exact atom-level response.  The free clock poles and phase speed are

```text
x_(a,k)=(k+1/2)pi/a,
phi_0'(x_(a,k))=2a tanh(a),
mu_(a,k)^free=coth(a)/a.                                  (21)
```

If `x_(a,k)(epsilon)` is the continued pole, implicit differentiation of
`Theta_epsilon(x_(a,k)(epsilon))=1` gives

```text
dot x_(a,k)=-Delta_a(x_(a,k))/(2ia tanh(a)).              (22)
```

The free phase speed is stationary in `x` at each clock pole.  Differentiating
`mu=2/phi'` therefore yields

```text
dot mu_(a,k)=i Delta_a'(x_(a,k))/(2a^2 tanh(a)^2).         (23)
```

For the Donoghue probability atom `p=mu/(1+x^2)`,

```text
dot p_(a,k)
 =dot mu_(a,k)/(1+x_(a,k)^2)
  -2x_(a,k)mu_(a,k)^free dot x_(a,k)/(1+x_(a,k)^2)^2.     (24)
```

Equations `(22)--(24)` identify, pole by pole, how the restricted-Weil source deforms clock
locations and weights before any cofinal limit is taken.

## 5. Proof of Theorem B

The source-vector derivative is the exact identity

```text
[(I+epsilon A_a)^(-1)e^x-e^x]/epsilon
 =-(I+epsilon A_a)^(-1)A_a e^x -> -A_a e^x.
```

Uniform boundedness of the Fourier functionals on compact `z`-sets gives `(15)`.
Logarithmic differentiation of the quotient in `(16)` gives

```text
dot Theta/Theta
 =-H_a(z)/F_0(z)+H_a(-z)/F_0(-z)=Delta_a(z),              (25)
```

which is `(17)`.  The derivative of `i(1+w)/(1-w)` is `2i/(1-w)^2`, proving `(18)`.
Since `Delta_a(0)=0`, differentiating `(18)` at zero, where `Theta_a^free(0)=-1`, gives
`dot m_a'(0)=i h_a'(0)`.  Expanding `h_a'= (H_a'F_0-H_aF_0')/F_0^2` proves `(20)`.

At a free pole, `Theta_a^free=1` and `(Theta_a^free)'=2ia tanh(a)`.  This proves `(22)`.
Writing the boundary logarithmic derivative as `phi'=-i Theta'/Theta`, inserting `(17)`, and
using `(phi_0')'(x_(a,k))=0` gives `dot phi'=-i Delta_a'`; differentiating `2/phi'` proves
`(23)`, and the quotient rule proves `(24)`.

## 6. Scientific consequence

The far-negative boundary is no longer only a universal no-go.  It has a canonical arithmetic
outgoing direction:

```text
A_a
 -> H_a/F_0
 -> anti-reflected tangent Delta_a
 -> pole velocities and weight velocities
 -> complete projective inverse-moment response.          (26)
```

This is the first exact source producer for non-clock deformation in the Suzuki route.  It converts
the restricted-Weil operator directly into observable motion of the Donoghue spectrum.  The full
odd germ at zero is faithful to the entire even defect measure, so no finite-support or finite-jet
ambiguity remains after all orders are retained.

The live frontier is now precise: prove that the tangent field `Delta_a` has a source-derived
nonzero component which survives on an intrinsic cofinal intermediate shift schedule, then identify
the resulting atom motion with the Xi divisor.  Equations `(17)--(24)` provide the exact quantity
that such a theorem must propagate; generic Clark theory does not.

## 7. Hostile audit

1. **Classical parent theory.** Resolvent differentiation, quotient perturbation, Clark residues,
   and compact moment determinacy are classical.  Candidate novelty is their exact synthesis for
   Suzuki's restricted-Weil source, especially `(17)`, `(20)`, and the clock response `(22)--(24)`.
2. **Nonzero tangent is now proved.** The companion boundary-log theorem proves `Delta_a` is not
   identically zero for every fixed aperture.  Uniform cofinal survival remains open.
3. **No RH-bearing shift.** The expansion is taken at `lambda=-infinity` through
   `epsilon=(-lambda)^(-1)`.  It never inserts `lambda=0`.
4. **No finite-jet overclaim.** A finite prefix does not determine the measure.  Faithfulness uses
   every odd derivative plus compact determinacy of the reciprocal-square pushforward.
5. **No hidden zero atom.** The even extension divisor excludes zero; otherwise `(2)` would be
   undefined and the theorem would not apply.
6. **No cofinal conclusion.** A nonzero fixed-aperture tangent does not by itself prevent later
   homogenization.  The exact open core is persistence of `(26)` on one intrinsic schedule.

## 8. Literature and priority audit

- Suzuki's 2026 paper constructs the shifted finite-aperture characteristic family and states the
  cofinal spectral limit as a conjectural direction, but does not derive `(5)--(24)`.
- Livšic--Donoghue and Clark theory classically relate characteristic functions, Herglotz functions,
  spectral measures, residues, and phase derivatives.
- Search through 2026-07-21 found no Suzuki follow-up deriving a restricted-Weil free-boundary
  tangent, inverse-moment reconstruction, or clock atom-response law.
- Specialist priority review remains required.

## 9. Formalization target

Formalize the dependency-closed analytic core in
`formal/GaloisForLFunctions/RHTower/SuzukiArithmeticTangentHolography.lean`:

```text
iteratedDeriv_suzukiDonoghueTransform_odd_zero
suzukiInverseMomentReconstruction_eq
suzukiProjectiveMomentShape_geometricScale
hasDerivAt_suzukiFourierLivsic_freeBoundary
hasDerivAt_suzukiUpperCayleyInv_parameter
hasDerivAt_suzukiHerglotz_freeBoundary
```

The concrete operator expansion `(15)` and measure pushforward determinacy stay paper-level until
the restricted-Weil operator is represented in Lean.  They must not be replaced by an axiom or an
abstract wrapper claiming source construction.

## 10. Gates

- [x] exact odd-jet/inverse-moment law proved
- [x] complete projective determinacy proved
- [x] free first two inverse moments derived
- [x] restricted-Weil tangent derived
- [x] pole and atom response derived
- [x] RH circularity and projective-scalar attacks closed
- [x] current primary-source and literature search completed
- [x] scratch Lean proof of analytic connectors completed
- [ ] source nonvanishing/persistence theorem
- [ ] intrinsic cofinal intermediate shift
- [ ] Xi divisor weld
- [ ] specialist novelty review
- [ ] RH

### Lean progress — compact moment determinacy FORMALIZED

Section 9 parks two items: the concrete operator expansion `(15)`, and *"measure pushforward
determinacy"*, both "until the restricted-Weil operator is represented in Lean". The second does not
depend on the operator at all: determinacy of a **compactly supported** measure by its moments is a
statement about the measure alone, and the hostile audit's item 4 uses it exactly in that form
("compact determinacy of the reciprocal-square pushforward"). It is now proved.

New module `HTGeometry/CompactMomentDeterminacy.lean` [PROVED HERE], wired into the `HTGeometry`
umbrella, standard axioms `[propext, Classical.choice, Quot.sound]`, builds clean:

- `integrable_of_continuous` : a continuous function on a compact space is integrable against a
  finite measure.
- `continuous_integral_continuousMap` : integration against a finite measure is Lipschitz with
  constant `rho(univ)` on `C(X, ℝ)` for compact `X`, hence continuous.
- `ext_of_forall_integral_pow_eq` : **the determinacy theorem** — two finite measures on `Icc a b`
  with the same moments are equal. Mechanism: equal moments give equal integrals of every
  polynomial (`Polynomial.eval_eq_sum_range` plus termwise integrability); Weierstrass
  (`polynomialFunctions_closure_eq_top`) makes the polynomial functions dense in `C(Icc a b, ℝ)`;
  two continuous functionals agreeing on a dense set are equal; and
  `ext_of_forall_integral_eq_of_IsFiniteMeasure` converts that into equality of measures.

mathlib has both ingredients (Weierstrass, and the bounded-continuous extensionality of finite
measures) but not the determinacy statement itself, so this is corpus-owned and reusable — the
statement quantifies over an arbitrary finite measure on the interval, so it applies verbatim to a
pushforward. The remaining paper-level item on this card is `(15)` alone.

### Cross-reference — `(15)`'s convergence is now a corpus theorem

Section 9 parks "the concrete operator expansion `(15)`" on a Lean representation of the
restricted-Weil operator. Its own proof (Section 5) reduces `(15)` to

```text
[(I + eps A_a)^{-1} e^x - e^x] / eps = -(I + eps A_a)^{-1} A_a e^x -> -A_a e^x,
```

i.e. to the **strong** convergence `(I + eps A_a)^{-1} -> I` evaluated at the fixed vector
`A_a e^x`. That statement is now unconditional in the corpus:

- `RHTower/SuzukiStrongResolventLimit.lean` : `tendsto_neumannShiftFamily_id` —
  `(I + eps A)^{-1} v -> v` strongly as `eps -> 0+`, for `A = rho + B^{-1}` with `B` the bounded,
  injective, self-adjoint resolvent. No unbounded operator is formed anywhere in its proof.

Instantiating at `v = A_a e^x` gives `(15)`'s limit directly. The remaining input is not analytic:
it is that `A_a e^x` exists at all, i.e. `e^x ∈ range B` — a domain hypothesis about Suzuki's
operator. The identity `[(I + eps A)^{-1} - I]/eps = -(I + eps A)^{-1} A` used to get there is pure
algebra, and the bounded-operator expansion behind it is mathlib's `NormedRing.inverse_add`.

Together with the moment-determinacy entry above, both of this card's parked items are now traced to
naming the source rather than constructing the operator.

### Lean progress — `(18)`'s derivative FORMALIZED

Section 5 proves `(18)` from "the derivative of `i(1+w)/(1-w)` is `2i/(1-w)^2`". The corpus already
had that transform as `herglotzOfCayley` but no derivative for it; it is now proved in
`RHTower/SuzukiDonoghueHerglotzTransform.lean` [PROVED HERE], standard axioms
`[propext, Classical.choice, Quot.sound]`, builds clean:

- `hasDerivAt_herglotzOfCayley` : `HasDerivAt herglotzOfCayley (2 I / (1 - Θ)^2) Θ` for `Θ ≠ 1`.

This is the factor converting a logarithmic derivative of the characteristic into a derivative of
the Herglotz function, so with `(25)`/`(17)` it supplies `(18)` directly.

### `(17)`/`(25)` need no new Lean — mathlib has the logarithmic derivative

Section 5 obtains `(17)` by "logarithmic differentiation of the quotient in `(16)`", giving
`dot Theta / Theta = -H_a(z)/F_0(z) + H_a(-z)/F_0(-z)`. That step is mathlib's, not ours:

- `Mathlib/Analysis/Calculus/LogDeriv.lean` : `logDeriv_div (x) (hf : f x ≠ 0) (hg : g x ≠ 0) ...`
  — the logarithmic derivative of a quotient is the difference of the logarithmic derivatives,
  under exactly the nonvanishing hypotheses `(16)` already carries.

So `(17)` reduces to supplying `F_0(z) ≠ 0` and `F_0(-z) ≠ 0` on the relevant set and applying it;
with `hasDerivAt_herglotzOfCayley` above supplying `(18)`, the whole `(16)`--`(18)` block is
mathlib plus one corpus lemma. Nothing here requires the operator.

- `differentiableAt_herglotzOfCayley` : the transform is differentiable away from `Θ = 1` — the form
  the chain rule needs when it is composed with a characteristic, as `(16)` does.
  [PROVED HERE], standard axioms, builds clean.
- `hasDerivAt_cayleyOfHerglotz`, `differentiableAt_cayleyOfHerglotz` : the same for the inverse
  transform, `d/dm [(m - I)/(m + I)] = 2I/(m + I)^2` away from `m = -I`. Both directions of the
  Cayley correspondence now carry derivatives, which is what `(16)`'s chain rule needs in either
  orientation. [PROVED HERE], standard axioms, builds clean.
- `hasDerivAt_herglotzOfCayley_comp` : the chain rule, `d/dz [m(Θ(z))] = 2I/(1 - Θ z)^2 * Θ'(z)` —
  the exact form `(16)`--`(18)` apply, with `(17)`'s logarithmic derivative supplying `Θ'/Θ` from
  mathlib's `logDeriv_div`. [PROVED HERE], standard axioms, builds clean.

With this the `(16)`--`(18)` block needs no further analytic infrastructure: transform derivatives in
both directions, the chain rule, and the quotient logarithmic derivative are all available. What
remains is supplying the nonvanishing side conditions `F_0(±z) ≠ 0` from the card's own setup.
- `hasDerivAt_cayleyOfHerglotz_comp` : the chain rule for the inverse direction, completing the
  pair. [PROVED HERE], standard axioms, builds clean.

The Cayley--Herglotz differential layer is now complete in both directions: derivative,
differentiability, and chain rule for each of `herglotzOfCayley` and `cayleyOfHerglotz`. Any of
`(16)`--`(18)`'s manipulations can be assembled from these plus mathlib's `logDeriv_div`.

### Section 9's module EXISTS — all six targets formal, and Theorem A's determinacy is end to end

`RHTower/SuzukiArithmeticTangentHolography.lean` now carries the card's entire dependency-closed
analytic core.  The six named targets:

- `iteratedDeriv_suzukiDonoghueTransform_odd_zero` — **`(5)`**: for a spectral probability with a
  gap `δ` about the origin, `m^{(2n+1)}(0) = (2n+1)! (q_n + q_{n+1})`.  The route is `(13)` as
  `hasDerivAt_suzukiCauchyPow`/`iteratedDeriv_suzukiCauchyPow` (differentiation under the Cauchy
  transform on the half-gap disc, dominated by the constant `(2/δ)^{j+1}`), then the Leibniz
  ladder `iteratedDeriv_succ_succ_suzukiDonoghueTransform` in which only the zeroth and second
  derivatives of `z²+1` survive.
- `suzukiInverseMomentReconstruction_eq` — **`(6)`**, the two-term recursion.
- `suzukiProjectiveMomentShape_geometricScale` — **`(8)`**: `κ_n` is invariant under every
  dilation `t ↦ ct`, `c ≠ 0`, via `suzukiInverseEvenMoment_dilation` (`q_n ↦ c^{-2n} q_n`).
- `hasDerivAt_suzukiFourierLivsic_freeBoundary` — **`(17)`/`(25)`**: the free-boundary tangent of
  the Livšic quotient is the quotient times the anti-reflected logarithmic derivative
  `Δ(z) = H(-z)/F(-z) - H(z)/F(z)`.
- `hasDerivAt_suzukiUpperCayleyInv_parameter` — the `2i/(1-w)²` transport factor of `(18)`.
- `hasDerivAt_suzukiHerglotz_freeBoundary` — **`(18)`**: `ṁ = 2i Θ_free Δ/(1-Θ_free)²`.

Beyond the six, the module closes what Section 9 had parked as "measure pushforward determinacy"
**completely**, not only for the pushforward:

- `suzukiInverseMoment_pushforward` — **`(7)`**: the moments of `ν.map (t ↦ (t²)⁻¹)` are the `q_n`.
- `map_invSq_eq_of_suzukiInverseMoments` — equal `q_n` identify the pushforward, through the
  compact interval `[0, δ⁻²]` and `HTGeometry/CompactMomentDeterminacy.ext_of_forall_integral_pow_eq`
  (subtype transfer by `MeasurableEmbedding.subtype_coe` both ways).
- `ext_of_even_of_map_invSq_eq` — **evenness recovers `ν`**: the preimage of a positive set under
  `t ↦ |t|` splits into two reflected copies of equal mass, so two even measures vanishing at the
  origin with the same `(t²)⁻¹`-pushforward are equal.
- `suzukiInverseMoment_determinacy` — **Theorem A's determinacy claim as one theorem**: an even
  finite measure with a spectral gap is determined by its inverse even moments.

All audit to exactly `[propext, Classical.choice, Quot.sound]`; umbrella wired.  What stays
paper-level is exactly what Section 9 says must not be wrapped: the concrete operator expansion
`(15)` (whose convergence half is already `tendsto_neumannShiftFamily_id`, leaving only the
domain fact `e^x ∈ Dom(A_a)` as source data) and Theorem B's identification with Suzuki's
operator — the folder's shared open-research core.
