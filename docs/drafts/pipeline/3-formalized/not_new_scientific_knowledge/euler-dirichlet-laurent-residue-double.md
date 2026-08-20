# The centered Euler source canonically generates its Laurent residue double

- **ID:** `euler-dirichlet-laurent-residue-double`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM / SOURCE-PURE HT LAURENT CHART
- **Scientific status:** `[PROVED HERE] [REAL-FREQUENCY CORE LEAN-FORMALIZED] [PARENT GROUP-COMPLETION AND CURRENT-ALGEBRA THEORY] [NOT AN RH PROOF]`
- **Parents:**
  - `../../1-in-progress/hypertranscendental-laurent-horizon-residue-field.md`;
  - `../../1-in-progress/source-polarized-laurent-pluecker-tangent-ward-law.md`;
  - `../squarefree-euler-modular-corona-curvature-colligation.md`.

## Statement

Center the spectral parameter by

```text
z=s-1/2.                                                   (1)
```

The positive Euler characters are

```text
chi_n^+(z)=n^(-z),       n in N_(>0).                     (2)
```

The multiplicative monoid `N_(>0)` is cancellative and its group completion is canonically
`Q_(>0)^x`.  Therefore the minimal multiplicative character algebra containing `(2)` and closed
under functional-equation reflection is

```text
A_E=C[Q_(>0)^x],
chi_q(z)=q^(-z),
rho chi_q=chi_(q^(-1)).                                   (3)
```

Indeed,

```text
chi_q(-z)=chi_(q^(-1))(z)=chi_q(z)^(-1).                  (4)
```

Thus the negative Laurent half is not introduced by a formal loop variable.  It is the reflected
group-completion half of the actual Euler Dirichlet monoid.

## Constant-term residue seam

Let `D` be the source scale derivation and `CT` the coefficient of the neutral rational character:

```text
D chi_q=-(log q)chi_q,
CT(sum_q a_q chi_q)=a_1.                                  (5)
```

Define

```text
omega_E(f,g)=CT(f Dg).                                    (6)
```

On pure modes,

```text
omega_E(chi_q,chi_r)
 =-(log r) if q r=1,
 =0        otherwise.                                    (7)
```

Since the constant term of `D(fg)` is zero,

```text
omega_E(f,g)=-omega_E(g,f).                               (8)
```

Tensoring with an invariant matrix trace gives the standard current-algebra cocycle

```text
Omega_E(X tensor f,Y tensor g)=trace(XY)omega_E(f,g).      (9)
```

Its Lie `2`-cocycle identity follows from the derivation law for `D`, invariance of the trace, and
`CT D=0`.

## Same-half isotropy and opposite-mode nondegeneracy

If `m,n>=1`, then `mn=1` only when `m=n=1`, where the logarithmic coefficient in `(7)` is zero.
Hence

```text
omega_E(chi_m,chi_n)=0.                                   (10)
```

The same argument applies to `chi_(m^(-1)),chi_(n^(-1))`.  Therefore both Euler halves are
residue-isotropic.

For every `n>1`, however,

```text
omega_E(chi_n,chi_(n^(-1)))=log n !=0.                    (11)
```

Thus every nontrivial positive Dirichlet mode pairs nondegenerately with its source-reflected
negative mode.  Prime unique factorization makes the character group equivalently the finite
integer prime-exponent lattice; the seam weight is the corresponding integer combination of prime
logarithms.

## Squarefree apartment specialization

For one prime and `s=1/2+z`, write

```text
Delta_p(z)=p^(-z).
```

The two source-reflected local factors are

```text
1+p^(-s)       =1+p^(-1/2)Delta_p(z),
1+p^(-(1-s))   =1+p^(-1/2)Delta_p(z)^(-1).               (12)
```

These are the positive and negative torsion charts of the same prime apartment.  Their overlap is
the exact opposite-mode seam `(11)` with weight `log p`.  Products over finite prime sets give the
finite squarefree determinant line and its reflected Laurent chart.

## No-go and positive theorem

**No-go.**  Projective inversion of the target horizon does not invert the source arc parameter and
cannot manufacture negative current modes.  An abstract Laurent variable added to the `A2`
building would fail the source-purity gate.

**Positive theorem.**  For the Euler source, centering at the fixed point of the functional
equation and group-completing the multiplicative Dirichlet monoid canonically produces the negative
half, its reflection, its derivation, and the nondegenerate residue seam.  The pointed Euler
translation groupoid retains the same multiplicative source increments after coarse continuous
quotients collapse, so the construction belongs to the pointed source rather than to a chosen
scalar coordinate.

This is stronger than saying that a Laurent double is available: it identifies the minimal
source-derived Laurent algebra and computes its central pairing exactly.

## RH consequence and remaining wall

The theorem closes the source-puncture and negative-mode gates for the squarefree Euler
specialization of the HT Laurent-horizon program.  It does not prove the Ward estimate.  The basic
residue metric weights a mode by its frequency `|log q|`, while the anti-causal RH bound uses the
one-particle `L2` capacity metric.  The remaining theorem is the source-polarized
Laurent--Pluecker tangent transgression which transports the first-trace central class into that
capacity metric.

## Gates

- [x] centered Euler positive character monoid identified
- [x] minimal reflected group completion identified with positive rational characters
- [x] source reflection proved to invert every character
- [x] scale derivation and constant-term functional constructed
- [x] same-half residue isotropy proved
- [x] every nontrivial opposite mode proved nondegenerately paired
- [x] squarefree prime-apartment charts recovered exactly
- [x] real-frequency characters, reflection, residue pairing, same-half isotropy, prime seams, and
      the `A2` Lie-cocycle identity formalized in
      `formal/GaloisForLFunctions/RHTower/EulerLaurentResidueDouble.lean`
- [ ] lift the scalar character double to the complete `A2` horizon current algebra in the Euler
      source realization
- [ ] construct the capacity-metric Pluecker tangent transgression
- [ ] RH

## Lean formalization completed (2026-08-21)

The real-frequency core was already in `formal/GaloisForLFunctions/RHTower/EulerLaurentResidueDouble.lean`
(`eulerLaurentCharacter`, `eulerLaurentCharacter_reflection`, `eulerLaurentCharacter_reflection_eq_inv`,
`eulerLaurentResidueWeight_swap`, `eulerLaurentResidueWeight_nonneg_zero`,
`eulerLaurentResidueWeight_nonpos_zero`, `eulerLaurentResidueWeight_opposite`,
`eulerPrimeLaurentResidueWeight_pos`, `eulerA2LaurentResiduePairing_cocycle`).

The remaining gates — the **group completion** `(3)`, the **scale derivation and constant-term
functional** `(5)`–`(6)`, and the **squarefree prime-apartment charts** `(12)` — are now formalized in
the new module

`formal/GaloisForLFunctions/RHTower/EulerCharacterGroupCompletion.lean`

(namespace `GaloisForLFunctions`; every declaration audited to `propext`, `Classical.choice`,
`Quot.sound` only):

- `EulerCharGroup` — the positive rationals as a `CommGroup` (mathlib's `Positive` subtype
  instances); `EulerCharGroup.ofNat` is the positive Dirichlet monoid inside it.
- `EulerCharGroup.exists_natCast_quotient`, `EulerCharGroup.closure_natRange_eq_top` — **`(3)`,
  minimality half**: the subgroup generated by the Euler Dirichlet monoid is all of `ℚ_{>0}^×`, so
  the reflected half is exactly the group completion of the actual monoid and nothing more.
- `EulerCharGroup.ofNat_mem_closure_primeRange`, `EulerCharGroup.closure_primeRange_eq_top` — the
  **prime-exponent lattice** description: by unique factorization the prime modes alone generate the
  character group.
- `eulerRatCharacter`, `eulerRatCharacter_mul`, `eulerRatCharacter_one` — `χ_q(z) = q^{-z}` is a
  monoid morphism, `(2)`.
- `eulerRatCharacter_reflection` (`χ_q(-z) = χ_{q^{-1}}(z)`),
  `eulerRatCharacter_reflection_eq_inv` (`χ_q(-z) = χ_q(z)^{-1}`) — **`(4)`**.
- `eulerRatCharacter_injective` — the character map is injective, so the character algebra is
  canonically the group algebra `ℂ[ℚ_{>0}^×]`.
- `EulerCharAlgebra := MonoidAlgebra ℂ EulerCharGroup`, `scaleWeight`, `scaleDeriv`,
  `scaleDeriv_coeff`, `scaleDeriv_single`, `scaleDeriv_add`, **`scaleDeriv_mul`** (the Leibniz rule),
  `constantTerm`, `constantTerm_add`, **`constantTerm_scaleDeriv`** (`CT ∘ D = 0`) — **`(5)`**.
- `residuePairing` (`ω_E(f,g) = CT(f · Dg)`), `residuePairing_single` — **`(7)`** exactly:
  `ω_E(χ_q, χ_r) = -log r` if `q r = 1`, else `0`.
- `residuePairing_swap` — **`(8)`**, the alternating law, derived from Leibniz plus `CT ∘ D = 0`.
- `residuePairing_natMode_eq_zero` — **`(10)`**, same-half isotropy.
- `residuePairing_opposite`, `residuePairing_opposite_ne_zero` — **`(11)`**, exact weight `log q` and
  nondegeneracy of every nontrivial opposite pair.
- `cpow_neg_eq_eulerRatCharacter`, `eulerPrimeApartmentChart`,
  `eulerPrimeApartmentChart_reflected` — **`(12)`**, the two source-reflected squarefree local
  factors as the positive and negative torsion charts of the same prime apartment.

Wired into `GaloisForLFunctions.RHTower`.

## Gates

- [x] group completion and its minimality formalized (`closure_natRange_eq_top`)
- [x] prime-exponent lattice generation formalized (`closure_primeRange_eq_top`)
- [x] scale derivation, Leibniz rule and constant-term functional formalized
- [x] residue pairing, alternating law, isotropy and nondegeneracy formalized
- [x] squarefree prime-apartment charts formalized

The three unchecked gates above (`A₂` horizon current algebra lift, capacity-metric Plücker
transgression, RH) are the card's own **open research targets**, not proven theorems.
