# The reflection-torsion law

**Status:** core Lean-closed (axiom-clean), open core stated.
**Module:** `formal/GaloisForLFunctions/RHTower/LagReflectionKernelNoGo.lean`, wired into
`GaloisForLFunctions/RHTower.lean`.
**Ledger:** CANNOT-397, MUST-398.

## The two kernels

On the multiplicative group of positive reals the lag function `Φ` (`Φ(L) = Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))`,
certified prime side) gives two kernels:

| | entries | shape | status |
|---|---|---|---|
| translation | `K(x,y) = Φ(log x − log y)` | Toeplitz, ratios | PSD ⟺ RH (corpus) |
| reflection | `K♯(x,y) = Φ(log x + log y)` | Hankel, products | **never PSD** (this card) |

`K♯(x,y) = K(x, y⁻¹)` — `lagReflectionKernel_eq_lagGramKernel_inv`, with no positivity hypothesis
on either argument. So the reflection kernel is the translation kernel composed with the group
inversion, and the two agree along a column exactly at a fixed point of the inversion.

## The theorem

1. `lagReflectionKernel_self` : `K♯(x,x) = Φ(log x²)` — **the reflection diagonal is the lag
   function on the squares.**
2. `exists_lagReflectionKernel_self_neg` : some `x > 0` has `K♯(x,x) < 0`, **unconditionally**.
   Witness `x = √n` for any `n` realising the corpus's unconditional `Ω₋` law for the integer lags.
3. `not_forall_lagReflectionKernel_self_nonneg` : hence `K♯` is not PSD.
4. `lagGramKernel_self_pos` : by contrast `K(x,x) = 2 + γ − log 4π > 0` at every `x`.
5. `lagReflection_antipodal_form` : on `{x, x⁻¹}` with weights `(1,−1)`,
   `K♯(x,x) − 2K♯(x,x⁻¹) + K♯(x⁻¹,x⁻¹) = 2(Φ(log x²) − Φ(0))`.
6. `lagReflection_antipodal_form_nonpos_of_riemannHypothesis` : **under RH that form is `≤ 0` for
   every `x`**, because RH makes `Φ(0)` the supremum of `Φ`.
7. `inv_eq_self_iff_one` : the 2-torsion of `ℝ_{>0}` is `{1}`.

All eight declarations audit to `[propext, Classical.choice, Quot.sound]`.

## What it changes

The previous cycle's terminus was: *free = Toeplitz = `C²+S²`; needed = Hankel = `C²−S²`; supply the
reflection positivity as data.* Item 6 says that on this carrier the datum cannot be supplied,
because RH itself makes the reflection form negative semidefinite in the inversion directions. The
obstruction is not analytic and not arithmetic — it is that `ℝ_{>0}` and `ℚ^×_{>0}` are **torsion
free**. Reflection positivity is a statement about the fixed locus of an involution; on a torsion-free
group that locus is a point.

## Open core

Construct, before divisor specialisation, a carrier on which
(i) the inversion has a large fixed set (abundant 2-torsion),
(ii) the valuation grading of `ℚ^×_{>0}` is retained (the square-class quotient `⊕_p 𝔽₂` destroys it:
     there the inversion is the identity, the two kernels coincide, and no RH-strength condition
     survives),
(iii) the lag kernel descends, and
(iv) the reflection form on it is positive.

Two candidate directions, both forced by the law rather than chosen:
- **Archimedean.** The only nontrivial involution `ℚ^×` acquires is the sign, at the archimedean
  place. The corpus's repeated "prime and archimedean organs are sampling-disjoint" is then the same
  statement: the reflection's whole fixed locus is archimedean.
- **Congruence.** At modulus `q` the functional equation is the inversion of the reduced residues
  (fixed set of size `2^{ω(q)}`), whose additive-Fourier matrix is the normalised Kloosterman matrix
  — maximally flat away from the zero-frequency row. The fixed set grows with `ω(q)`; level one is
  the degenerate member where the involution is a scalar.

## Falsifiers

- If some corpus criterion of Hankel shape is actually stated with the *ratio* kernel, item 6 does
  not apply to it; check each before quoting this card.
- If a carrier is proposed with 2-torsion but the lag kernel does not descend to it, (iii) fails and
  the construction is void.
- If the 2-torsion is supplied only after reading a zero, the construction is circular and falls
  under the corpus's standing post-divisor prohibition.
