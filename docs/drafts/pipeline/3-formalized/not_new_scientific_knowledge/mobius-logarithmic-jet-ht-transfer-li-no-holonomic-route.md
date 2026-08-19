# Möbius logarithmic jets preserve hypertranscendence; Li coefficients are not holonomic

- **ID:** `mobius-logarithmic-jet-ht-transfer-li-no-holonomic-route`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / route no-go
- **Scientific status:** `[PROVED HERE] [UNCONDITIONAL] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; coefficient transforms; Li-criterion boundary
- **Statement:** For a nonzero meromorphic function, logarithmic differentiation after a Möbius
  change preserves DA versus HT exactly.  Independently, a function with infinitely many zeros has
  a non-D-finite Möbius logarithmic jet.  Consequently the Li sequence is unconditionally not
  P-recursive, and no holonomic closed-recurrence implementation of Li's criterion can prove RH.
  The independently proved augmentation-exposure theorem makes completed `xi` HT, so its Li
  generator is unconditionally HT as well.

## Goal

Find an exact point at which hypertranscendence excludes a literature route rather than merely
making it difficult.  Li's criterion itself is equivalent to RH and cannot honestly be declared
incapable of proving RH.  The theorem instead isolates and kills a concrete implementation found in
the Li literature: close the Li coefficients under a finite linear recurrence with polynomial
coefficients and prove positivity inductively.

The no-go is deliberately limited to a **closed holonomic recurrence**.  Recurrences with a new
zero-sum forcing term at every index, integral/norm representations, Weil positivity, and genuinely
infinite-dimensional arguments remain possible.

## General transfer theorem `[PROVED HERE]`

Let `K=C(z)`, let `F` be a nonzero meromorphic function, and let

`r(z)=(az+b)/(cz+d)`, `ad-bc != 0`,

be a nonconstant Möbius transformation with rational inverse `q`.  Define the Möbius logarithmic
jet

`J_r(F)(z)=r'(z) F'(r(z))/F(r(z))`.

Then

`F is DA over C(z) iff J_r(F) is DA over C(z)`.

Equivalently,

`F is HT over C(z) iff J_r(F) is HT over C(z)`.

On every simply connected zero-free germ on which a logarithm is chosen, these are also equivalent
to differential algebraicity or hypertranscendence of `log(F o r)`.

### Forward implication

If `F` is DA, so are `F'`, `1/F`, and `F'/F`.  The DA meromorphic functions form a differential
field and are closed under composition with a rational function.  Multiplication by the rational
function `r'` shows that `J_r(F)` is DA.

### Reverse implication

Suppose `J_r(F)` is DA.  Substitute `z=q(w)`.  Since `q` is rational and

`r'(q(w)) q'(w)=1`,

one obtains

`F'(w)/F(w)=q'(w) J_r(F)(q(w))`.

The right side is DA.  Thus `F` solves the first-order linear equation

`Y' = u Y`, `u=F'/F`,

over a DA differential extension of `C(w)`.  Hence `F` is DA over that extension, and transitivity
of differential algebraicity makes `F` DA over `C(w)`.

For a local logarithm `G=log(F o r)`, one has `G'=J_r(F)`.  Differentiation preserves DA, while an
ADE for `G'` becomes an ADE for `G` after shifting every derivative index by one.  Therefore `G` is
DA exactly when `J_r(F)` is DA.  This completes all equivalences.  ∎

## Li specialization `[PROVED HERE, UNCONDITIONAL]`

Let `xi` be Riemann's completed xi-function and put

`r(z)=1/(1-z)`, `q(w)=1-1/w`.

Near `z=0`, the Keiper--Li generating identity is

`log xi(1/(1-z)) = log xi(1) + sum_(n>=1) (lambda_n/n) z^n`.

Consequently

`L_Li(z):=sum_(n>=1) lambda_n z^(n-1)`

`=d/dz log xi(1/(1-z))`

`=(1-z)^(-2) xi'(1/(1-z))/xi(1/(1-z))`

`=J_r(xi)(z)`.

The completed-logarithmic-derivative augmentation theorem proves unconditionally that `xi'/xi` is
HT over `C(s)`: applying the shift `s -> s+2` strips the common gamma mode and exposes an ordinary
Dirichlet series with nonzero coefficients at every prime, to which Ostrowski applies.  The
logarithmic-derivative equivalence then makes `xi` HT.  Applying the transfer theorem gives

`L_Li is HT over C(z)`.

The integrated Keiper--Li series `sum lambda_n z^n/n` is HT as well.

## Infinite-divisor obstruction to holonomicity `[PROVED HERE]`

Let `F` be a nonzero entire function with infinitely many distinct zeros, and let `r` be a Möbius
transformation.  Then `J_r(F)` is not D-finite over `C(z)`.

Indeed, `F'/F` has a pole at every zero of `F`, with residue equal to its positive multiplicity.
Möbius transformations are injective and have nonvanishing derivative away from their single pole,
so `J_r(F)` has poles at infinitely many distinct finite inverse images of zeros of `F` (discarding
at most the one zero mapped to infinity).

By contrast, an analytic germ satisfying a linear differential equation with polynomial
coefficients can have finite-plane singularities only among the finitely many zeros of the leading
coefficient.  It analytically continues along every path avoiding that finite set.  Therefore a
D-finite germ cannot have infinitely many distinct finite poles.  Hence `J_r(F)` is not D-finite. ∎

This obstruction is strictly weaker than hypertranscendence: `tan` and logarithmic derivatives of
many DA entire functions are DA but not D-finite.  It is nevertheless exactly strong enough for a
closed linear-recurrence no-go.

## Holonomic Li-route no-go `[PROVED HERE, UNCONDITIONAL]`

A sequence is P-recursive precisely when its ordinary generating function is D-finite: there are
fixed polynomials `p_0(n),...,p_m(n)`, not all zero, such that

`sum_(j=0)^m p_j(n) lambda_(n+j)=0`

for all sufficiently large `n` if and only if its generating series satisfies a nonzero linear ODE
with polynomial coefficients.  Every D-finite function is DA.

The completed `xi` has infinitely many distinct nontrivial zeros.  The divisor obstruction applied
to `r(z)=1/(1-z)` proves unconditionally that `L_Li` is not D-finite.  Hence the Li coefficients are
not P-recursive.  Therefore:

> No proof of RH through Li's criterion can close the full Li sequence into a finite linear
> polynomial-coefficient recurrence and then deduce positivity from that recurrence.

This is an impossibility theorem, not a statement that recurrence identities are useless.  Huan
Xiao's published recurrences contain a new zero-power-sum forcing term at every `n`; the theorem
explains why that forcing cannot be eliminated into a fixed closed P-recursive law for the
`lambda_n` alone.

## Attack as false

1. **Kill the broad claim.** `Li's criterion cannot prove RH` is false as a formulation: the
   criterion is equivalent to RH.  Only the holonomic closed-recurrence implementation is excluded.
2. **Nonlinear finite recurrences.** A finite nonlinear recurrence for consecutive values need not
   have a D-algebraic generating function.  The theorem does not exclude arbitrary nonlinear
   recurrences; saying so would overreach.
3. **Inhomogeneous forcing.** A recurrence involving fresh zero sums, prime sums, or other
   infinite-dimensional input at each index is not closed and is not excluded.
4. **Asymptotic recurrences.** An asymptotic expansion or inequality is not an exact P-recurrence and
   remains available.
5. **Source dependence, audit result.** Li--Ye 2008 alone does not source-clear `HT(xi)`; it proves
   only a restricted class of joint polynomial nonrelations and presents full differential
   independence of `zeta` and `Gamma` as Markus's conjecture.  The unconditional input now comes
   instead from the completed-logarithmic-derivative augmentation theorem, whose Ostrowski source
   exposure avoids the missing joint-independence claim.

## Scientific gate

The unconditional Möbius logarithmic-jet equivalence is a short consequence of standard DA field closure,
rational substitution, and transitivity.  The P-recursive corollary is then standard holonomic
duality plus the classical finite-singularity property of linear ODEs.  It is useful and theorem-level,
but the anti-theatre gate currently grades it `[BRIDGE]`,
not new scientific knowledge.  Its role is to turn the independently new entire-cascade law into a
clean landscape boundary: neither the function nor its Li logarithmic coordinate admits a finite
algebraic-differential handle.

## Gates

- [x] 0 -> 1: exact transform, exact no-go class, broad-route overclaim explicitly falsified.
- [x] Paper proof of the general transfer theorem.
- [x] Unconditional paper proof that the Li generator is not D-finite and the Li sequence is not
  P-recursive.
- [x] Unconditional strengthening: `HT(xi)` and therefore the Li generator is HT.
- [x] Audit Li--Ye 2008 in full: it does not prove full differential independence and does not
  source-clear `HT(xi)`.
- [x] Prove `HT(xi)` independently of the unproved Markus joint-independence conjecture; discharged
  by `completed-logderiv-augmentation-filter-exposure.md` using a source-stripping shift and
  Ostrowski's theorem.
- [x] Search exact and equivalent non-holonomicity statements for the Li sequence; no exact primary
  statement located, but the proof is a routine finite-singularity argument and is graded bridge.
- [x] 1 -> 2: proof complete; parent/literature verdict `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.
- [ ] Lean only if the concrete analytic transform can be represented faithfully; the current
  pointwise HT definition lacks DA field-closure and composition infrastructure.

## Primary literature under audit

1. X.-J. Li, *The Positivity of a Sequence of Numbers and the Riemann Hypothesis*, J. Number Theory
   65 (1997), 325--333.
2. H. Xiao, *Recurrence Relations of Li Coefficients*, arXiv:2006.13103 (2020).
3. B. Q. Li and Z. Ye, *On Differential Independence of the Riemann Zeta Function and the Euler
   Gamma Function*, Acta Arith. 135 (2008), 333--337.
4. J. C. Lagarias, *Li Coefficients for Automorphic L-Functions*, Ann. Inst. Fourier 57 (2007),
   1689--1740.

## Log

- 2026-07-11 -- Created after rejecting categorical no-go claims for RH-equivalent routes.  Proved
  exact DA/HT preservation under the Möbius logarithmic-jet transform and isolated the resulting
  closed-holonomic Li recurrence impossibility.
- 2026-07-11 -- Full-text source audit corrected the project premise: Li--Ye 2008 proves a
  restricted class of joint nonrelations and states full `zeta`--`Gamma` differential independence
  as a conjecture.  The Li conclusion is therefore conditional on `HT(xi)`.
- 2026-07-11 -- Separated the claims.  Infinite zeros give infinitely many logarithmic-derivative
  poles, whereas a D-finite germ has only finitely many possible finite singularities.  Therefore
  the Li sequence is unconditionally non-P-recursive; only the stronger HT label remains
  conditional on `HT(xi)`.
- 2026-07-11 -- Exact P-recursive/holonomic searches found recurrence, asymptotic, norm, and Weil
  formulations but no exact printed non-P-recursiveness statement.  The result is nevertheless a
  direct classical singularity argument, so it is moved to fully-proven bridge infrastructure, not
  promoted as new science.
- 2026-07-11 -- Removed the conditional HT label after the independent augmentation-exposure
  theorem proved `xi'/xi`, hence `xi`, hypertranscendental without using the unproved joint
  differential independence of `zeta` and `Gamma`.  The Li logarithmic generator is now
  unconditionally HT; the card remains stage 2 because this complete analytic transfer has not
  been formalized in Lean.

## Lean formalization (complete, unconditional)

All four theorems of this card are machine-checked with no added axioms
(`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`).

**General transfer theorem** — `formal/GaloisForLFunctions/HTGeometry/MobiusJetTransfer.lean`.
The algebraic content of "logarithmic differentiation after a Möbius change preserves DA versus
HT exactly" is stated for an arbitrary characteristic-zero differential field extension:

- `DifferentialRescaledEquiv F E` — a field automorphism of `E` carrying the coefficient field `F`
  onto itself and intertwining the derivation up to a nonzero factor of `F`.  This is exactly the
  algebraic shadow of substitution by a nonconstant rational change of variable, for which
  `(f ∘ r)' = r' · (f' ∘ r)`.
- `exists_triangular_expansion` — the iterated derivatives of `σ x` are a triangular combination
  of the images of the iterated derivatives of `x`, with diagonal the powers of the factor.
- `differentialAlgebraicOver_map_iff` / `hypertranscendentalOver_map_iff` — exact invariance of
  differential algebraicity and hypertranscendence under the substitution.
- `mobiusJet_eq_logDeriv` — `J_r(F) = r' · (F'/F) ∘ r` equals `(F ∘ r)'/(F ∘ r)`.
- `hypertranscendentalOver_mobiusJet_iff`, `differentialAlgebraicOver_mobiusJet_iff` — the
  transfer theorem itself, obtained by composing the substitution invariance with the exact
  logarithmic-derivative equivalence `hypertranscendentalOver_deriv_div_self_iff`.

**The concrete analytic transform** — `HTGeometry/AnharmonicRatFunc.lean` and
`HTGeometry/AnharmonicMeromorphicSubstitution.lean`.  The chart `r z = 1/(1-z)` has order three
and permutes `{0, 1, ∞}`, so it restricts to an analytic automorphism of `ℂ ∖ {0,1}` with inverse
`r² z = 1 - 1/z`.  Precomposition is a field automorphism of the meromorphic function field of that
domain; the chain rule inserts the factor `r'(z) = (1-z)⁻²`, which is the rational function
`((1-X)⁻¹)²`.  The rational coordinate field `ℂ(z)` embeds as a differential base field, and
`anharmonicRescaledEquiv` assembles the data into a `DifferentialRescaledEquiv (RatFunc ℂ)
(meroField anharmonicDomain)`.  The Lean gate of this card — "only if the concrete analytic
transform can be represented faithfully" — is therefore discharged.

**Li specialization** — `RHTower/MobiusLiGeneratorHypertranscendence.lean`.

- `hypertranscendentalOver_xiAnharmonic` — `xi` is hypertranscendental over `ℂ(z)` inside that
  field; the identity theorem upgrades a relation on the open domain to a global relation, and
  `xi_hypertranscendental` supplies the global statement.
- `hypertranscendentalOver_liGeneratorMero` — **the Keiper--Li generator satisfies no algebraic
  differential equation over `ℂ(z)`**, unconditionally.
- `liGeneratorMero_mul_xiComp` and `liGenerator_eq_div` identify the field element with the
  quotient of the germs of `(xi ∘ r)'` and `xi ∘ r`, whose pointwise quotient is the analytic
  `liGenerator`.

**Non-holonomicity and the route no-go** —
`RHTower/MobiusLogarithmicJetLiGenerator.lean`.

- `liGenerator_eq_jet` — `L_Li(z) = (1-z)⁻² · (ξ'/ξ)(1/(1-z))`, the Möbius logarithmic jet.
- `liGenerator_not_holonomic` — a function with infinitely many nonzero zeros has a non-D-finite
  Möbius logarithmic jet, via the corpus residue engine.
- `xi_zeroSet_infinite`, `xi_zero_ne_zero`, and hence
  `liGenerator_not_holonomic_unconditional` — **the Li generating function satisfies no linear
  differential equation with polynomial coefficients**, so the Li sequence is not `P`-recursive
  and no holonomic closed-recurrence implementation of Li's criterion can prove RH.

- [x] Lean: complete and unconditional.
