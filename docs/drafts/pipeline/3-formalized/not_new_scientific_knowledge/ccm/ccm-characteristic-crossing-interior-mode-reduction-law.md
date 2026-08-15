# CCM screw null vectors reduce locally to finitely many characteristic modes

> **2026-07-22 domain correction.** This reduction applies to raw `L2` screw null vectors. The
> RH-bearing derivative zero fiber also contains possible vectors in Suzuki's completion outside
> raw `L2`; see `suzuki-completed-zero-mode-corona-seam-law.md`.

- **ID:** `ccm-characteristic-crossing-interior-mode-reduction-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** scalar Fourier multipliers and distributional constant-coefficient ODEs
- **Statement:** At every fixed aperture, an invertible pseudodifferential change of variable sends
  the interior trace of each CCM screw solution to an exponential polynomial generated exactly by
  the finitely many real zeros of the exact polar--Euler--Gamma symbol. Thus, conditional on the
  symbol's real characteristic set, the interior regularity problem is finite-dimensional; the
  remaining injectivity problem is a nonlocal boundary Evans relation coupling that packet to the
  exterior trace. No assertion that this real zero set is nonempty is made.

## 1. Truncated symbol

For fixed `a>0`, let

```text
P_a(xi)
 =[2sinh(a)cos(2a xi)+4xi cosh(a)sin(2a xi)]/(xi^2+1/4),

W_a(xi)
 =Re psi(1/4+i xi/2)-log pi
  -2 sum_(2<=n<=exp(2a))Lambda(n)n^(-1/2)cos(xi log n)
  +P_a(xi).                                             (1)
```

Here `P_a` is the Fourier transform of
`2cosh(t/2)1_(-2a,2a)(t)`, the exact aperture-truncated polar block. The apparent poles in its
displayed formula are removable. The sign and normalization are proved in
`ccm-polar-prime-critical-mellin-defect-law.md`. The complete symbol is real analytic on the real
axis and

```text
W_a(xi)=log|xi|+O_a(1)       as |xi|->infinity.          (2)
```

Hence its real zero set `Z_a` is finite. Indeed `(2)` confines all zeros to a compact interval,
and a nonzero real-analytic function has no accumulating zero in that interval.

For each `tau in Z_a`, let `nu_tau` be its analytic multiplicity and put

```text
p_a(xi)=product_(tau in Z_a)(xi-tau)^(nu_tau),
d_a=degree p_a.                                         (3)
```

Choose an integer `L_a` with `2L_a>=d_a` and define

```text
b_a(xi)=p_a(xi)/(1+xi^2)^(L_a),
c_a(xi)=W_a(xi)/b_a(xi).                                (4)
```

The quotient in `(4)` extends smoothly across every `tau`. It has no real zero, has at most
polynomial-logarithmic growth together with its derivatives, and tends in modulus to infinity or
to a positive nonzero asymptotic scale. After increasing `L_a` if necessary,

```text
inf_(xi in R)|c_a(xi)|>0.                               (5)
```

Thus `c_a(D)` is an injective tempered-distribution multiplier with inverse multiplier
`1/c_a`.

## 2. Interior characteristic-mode theorem

Let `I=(-a,a)` and let `u` be a compactly supported `L2` function such that

```text
W_a(D)u=0       in D'(I).                               (6)
```

Put

```text
v=c_a(D)u.                                              (7)
```

Then, on `I`,

```text
p_a(D)v=0.                                              (8)
```

Consequently

```text
v(x)=sum_(tau in Z_a)sum_(k=0)^(nu_tau-1)
       C_(tau,k)x^k exp(i tau x),       x in I,          (9)
```

in the distributional, hence classical, sense. The ambient ODE solution space containing all
attainable interior `v` traces has dimension exactly `d_a`; the attainable traces may form a proper
subspace because of the nonlocal exterior compatibility.

### Proof

Write `D=-i partial_x`. Fourier multipliers commute and `(4)` gives

```text
W_a(D)u=b_a(D)c_a(D)u=b_a(D)v.                          (10)
```

Equation `(6)` says that the last distribution vanishes on `I`. Apply the local differential
operator `(1+D^2)^(L_a)` on `I`. Since

```text
(1+D^2)^(L_a)b_a(D)=p_a(D),                             (11)
```

equations `(10)`--`(11)` prove `(8)`. The standard classification of distributional solutions of
a constant-coefficient ODE gives `(9)`.

## 3. Exact remaining boundary object

For a CCM null vector, equation `(6)` is supplemented by

```text
supp u subset [-a,a],
integral_(-a)^a u=0,
(G_a u)(0)=(G_a u)(a/2)=0.                              (12)
```

Not every exponential polynomial in `(9)` is the interior restriction of `c_a(D)u` for a vector
satisfying `(12)`. The inverse multiplier is nonlocal, and the interior coefficients do not by
themselves determine the exterior trace of `v`. Define the **characteristic Evans relation** to be
the set of pairs

```text
(interior coefficient packet (C_(tau,k)), exterior trace v|_(R\I))        (12a)
```

for which `u=c_a(D)^(-1)v` has support in `[-a,a]` and satisfies the three scalar conditions in
`(12)`.

Then

```text
ker G_a={0}
 iff the source-defined characteristic Evans relation has no nonzero
     compatible pair.                                                     (13)
```

Equation `(13)` is a definition of the exact remaining boundary object, not a claim that a
finite-dimensional determinant has already been constructed. The theorem proves only that its
interior trace is finite-dimensional and indexed canonically by the real characteristic crossings.
The exterior compatibility is irreducibly infinite-dimensional. The zero-free multiplier `c_a`
retains the infinite digamma pole lattice `plus_or_minus i(2n+1/2)`. Its exterior restriction is a
Hankel kernel; Kronecker's finite-rank theorem would make `c_a` rational if that restriction had
finite rank. Therefore the finite packet may appear as one block, but the complete Evans object
must begin as an operator/Fredholm relation on an infinite-dimensional Gamma boundary space. A
finite effective determinant is legitimate only after an exact Schur-complement elimination whose
entries retain the infinite block's resolvent. The proof is in
`ccm-characteristic-evans-boundary-infinite-rank-law.md`.

## 4. Positive CCM carrier law

If `W_a` has real zeros, they cannot be divided away and cannot be ignored as scalar sign changes.
Every successful screw-injectivity proof must carry the following exact alternative:

```text
zero-free corrected polar--Euler--Gamma symbol
  -> aperture factorization retaining the rank-two polar block,

or

finite real characteristic packet
  + inverse corrected multiplier
  + exterior trace and two-sided aperture support relation
  + mean-zero and affine anchors
  -> empty nonzero boundary Evans relation.             (14)
```

In the second branch the packet size `d_a` is allowed to grow with aperture. A fixed finite-state or
fixed-order scalar boundary rule cannot encode the exterior trace. A cofinal proof must construct
the infinite boundary operator and couple it to the growing finite packet. The earlier coarse
argument forcing crossings from the prime main term was invalid because it omitted
`P_a(0)=8sinh(a)`, which cancels that main term.

This is standard scalar multiplier and ODE reduction, so it is a bridge rather than new scientific
knowledge.

## Gates

- [x] real characteristic set proved finite at fixed aperture
- [x] exact aperture polar multiplier restored
- [x] bounded rational zero factor constructed
- [x] zero-free invertible multiplier isolated
- [x] interior null equation reduced to a constant-coefficient ODE
- [x] exact finite characteristic-mode packet identified
- [x] remaining boundary Evans relation, including exterior data, specified
- [x] exterior trace proved infinite-rank
- [x] raw finite characteristic-only Evans determinant retired
- [ ] decide whether the corrected symbol has real zeros at each aperture
- [ ] construct the infinite-dimensional Evans relation in a closed trace/boundary space
- [ ] construct an exact Schur complement retaining the infinite boundary resolvent
- [ ] prove its kernel is zero for every aperture
- [ ] RH

## Lean status

`[FORMALIZED]` — three modules, 49 theorems, all unconditional, axioms exactly
`[propext, Classical.choice, Quot.sound]`.

New infrastructure (absent from mathlib, built for this card and reusable):

- `formal/GaloisForLFunctions/HTGeometry/ExponentialPolynomialModes.lean` (22 declarations) — the
  **block calculus** of a constant-coefficient operator.  `blockOp L μ = L(derivative + μ)` is the
  action of `L(D)` on the polynomial factor of a block `P(x) e^{μ x}`
  (`realConstCoeffOp_polyExp`); its top coefficient is `L(μ)` times that of `P`
  (`coeff_blockOp`), whence `blockOp_ne_zero` at a nonroot and
  `natDegree_lt_rootMultiplicity_of_blockOp_eq_zero` at a root.  `eq_zero_of_sum_polyExp_eq_zero`
  proves that blocks with **distinct frequencies are linearly independent**, and
  `exists_characteristic_modes` upgrades the corpus statement "a smooth solution is *some*
  exponential polynomial" to the classical characteristic-mode theorem: the frequencies are exactly
  the roots of `L` and the degree at a root is strictly below its multiplicity.
- `formal/GaloisForLFunctions/HTGeometry/CharacteristicModeDimension.lean` (18 declarations) — the
  modes `x^k e^{μ x}` (`μ` a root, `k < ν_μ`) are linearly independent
  (`linearIndependent_charFamily`), they span the smooth solution space
  (`solutionSpace_eq_modeSpace`), and there are exactly `deg L` of them
  (`card_charIndex`), so **`finrank_solutionSpace : finrank ℂ (solutionSpace L) = L.natDegree`**.

Card module: `formal/GaloisForLFunctions/RHTower/CCMCharacteristicCrossingModes.lean`
(wired into `formal/GaloisForLFunctions/RHTower.lean`):

- `finite_realZeroSet_of_tendsto_atTop` — **equation (2)**: a real-analytic symbol tending to `+∞`
  at infinity has a finite real zero set.  Growth confines the zeros to a compact set and the corpus
  lemma `HTGeometry.finite_zeros_of_analyticOnNhd` finishes.  This is gate 1.
- `dampedFactor`, `localOperator_dampedFactor`, `dampedFactor_ne_zero` — **equations (3), (4),
  (11)**: `b_a = p_a/(1+ξ²)^{L_a}` and the exact restoration `(1+ξ²)^{L_a} b_a = p_a`.
- `symbolQuotient`, `symbolQuotient_mul` — **equation (4)**: `c_a = W_a/b_a` reproduces the symbol.
- `multiplier_injective`, `inverse_multiplier` — **equation (5)**: a symbol bounded away from zero
  is an injective multiplier with the explicit inverse multiplier `1/c_a`.
- `polynomial_symbol_eq_zero` — **equations (6), (7), (10), (11) ⟹ (8)**: on the symbol side the
  complete null equation becomes the polynomial null equation after the invertible change of
  variable.
- `modePoly`, `modePoly_ne_zero`, `natDegree_modePoly` — **equation (3)** in the derivative variable
  (`D = -i ∂` sends the real crossing `τ` to the frequency `i τ`), with degree `d_a = ∑_τ ν_τ`.
- `rootMultiplicity_modePoly` — **equation (9), multiplicities**: the multiplicity of the frequency
  `i τ` is exactly the analytic multiplicity `ν_τ` of the crossing.
- `realConstCoeffOp_charMode_modePoly` — **equation (9)**: every mode `x^k e^{i τ x}` with
  `k < ν_τ` solves the reduced interior equation.
- `exists_characteristic_packet` — **equation (9), exhaustiveness**: every smooth interior solution
  is a finite sum of such blocks.
- `finrank_characteristicPacket` — the card's dimension count: the ambient interior solution space
  has dimension exactly `d_a = ∑_τ ν_τ`.

Reused, not rebuilt: `HTGeometry.polyExp`, `expShiftPoly`, `deriv_polyExp`, `contDiff_polyExp`,
`expPolySpace` (`RealExponentialPolynomial`); `realConstCoeffOp`, `smoothSubmodule`,
`smoothDerivLM`, `coe_aeval_smoothDerivLM`, `mem_expPolySpace_of_realConstCoeffOp_eq_zero`
(`RealConstantCoefficientAnnihilator`); `expMonomialSpace`,
`exists_expMonomialSpace_of_mem_expPolySpace` (`AnseloneKorevaarTranslationRank`);
`finite_zeros_of_analyticOnNhd` (`RealAnalyticZeroFiniteness`).

Deliberately outside the Lean statement (cited analytic parents, not results of this card):

- The explicit symbol `(1)` with the digamma block, the prime sum and the aperture polar block
  `P_a`, together with its real analyticity and the asymptotic `(2)` itself.
- The smooth extension of `W_a/b_a` across each crossing and the uniform lower bound `(5)` for a
  large enough `L_a`.
- The localization of the multiplier identities to `D'(I)` and the passage from the distributional
  to the classical solution in `(9)`.
- The nonlocal exterior compatibility `(12)`–`(13)`, whose infinite rank is the separate card
  `ccm-characteristic-evans-boundary-infinite-rank-law.md`.
