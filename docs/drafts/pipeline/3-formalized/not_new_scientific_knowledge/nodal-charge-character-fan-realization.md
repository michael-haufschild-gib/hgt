# Nodal charges form a face-separated source-character fan

- **ID:** `nodal-charge-character-fan-realization`
- **Stage:** 2-fully-proven / algebraic-analytic core Lean-formalized
- **Type:** TYPED LOCAL REALIZATION / FACE-GLUING NO-GO / POSITIVE CHARACTER FAN
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED CORE] [BRIDGE]`
  `[PARENT FOURIER AND CHARACTER THEORY] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH RESULT]`
- **Source-face parent:**
  `source-face-observation-cohomology-transmutation.md`
- **Tate--Barnes parent:**
  `tate-theta-koszul-barnes-localization-transmutation.md`
- **Live successor:**
  `../../1-in-progress/hypertranscendental-source-face-vanishing-cycle-conservation.md`

## 1. The single-fibre proposal is too small

Fix a nonzero selected period `omega_j`.  The primitive nodal coordinate is

```text
x_j(z)=exp(2 pi i z/omega_j).
```

Its `m`-th power has differential frequency

```text
lambda_(j,m)=2 pi i m/omega_j.                                      (1)
```

Therefore different powers do not belong to one source-character fibre: differentiation has
eigenvalue `lambda_(j,m)`, and translation by a complementary period `omega_k` has eigenvalue

```text
chi_(j,m)(T_k)=exp(lambda_(j,m) omega_k).                            (2)
```

```text
[NO-GO]
A single one-dimensional Barnes character fibre cannot realize the complete integral nodal charge
lattice.  It realizes only one charge sector.
```

The positive replacement retains the grading.

## 2. Charge-graded local realization `[PROVED]`

Let

```text
ell_(j,m)(z)=exp(lambda_(j,m) z).                                   (3)
```

Then

```text
T_k ell_(j,m)=exp(lambda_(j,m) omega_k) ell_(j,m),
delta ell_(j,m)=lambda_(j,m) ell_(j,m),
(T_j-1)ell_(j,m)=0.                                                 (4)
```

For every finite set of distinct integers, the corresponding modes `(3)` are complex-linearly
independent.  Hence the algebraic local nodal receiver is the character-graded object

```text
Char_j=directSum_(m in Z) C_(chi_(j,m)),                            (5)
```

not an ungraded line.  The face module `B_j=D_N/(T_j-1)` has a character fibre at every
`chi_(j,m)`, and `(4)` gives the correctly typed realization

```text
B_j tensor_(chi_(j,m)) C  ->  C ell_(j,m),
1                         |-> ell_(j,m).                            (6)
```

The Tate-theta factorization from the parent card gives `E_(t^4)=x_j u` with `u` a unit.  Its
`m`-th power therefore has nodal localization class `[x_j^m]` and lands in the `m`-th sector of
`(5)`.  Equations `(1)`--`(6)` preserve charge, the selected annihilator, every complementary
translation phase, and the differential eigenvalue.  This is a typed local source-module
realization, not equality of integer labels.

Charge reversal is exact:

```text
lambda_(j,-m)=-lambda_(j,m),
ell_(j,-m) ell_(j,m)=1.                                             (6+)
```

Thus orientation reversal permutes the unpolarized character lines and exchanges every line with
its multiplicative dual.  Forgetting the charge chamber or opposite-line pairing necessarily makes
the whole object orientation-blind.

## 3. Different faces do not glue by equality `[PROVED]`

Let `omega_0,omega_1` be rationally independent.  If

```text
lambda_(0,m)=lambda_(1,n),                                         (7)
```

then the common frequency has trivial exponential character on both periods.  Rational
independence forces the frequency to vanish, and injectivity of `(1)` forces

```text
m=n=0.                                                             (8)
```

Thus the two charge spectra meet only in the neutral character.

```text
[NO-GO]
For incommensurate source faces, nonzero local charge lines cannot be glued by identifying their
characters.  A global realization built as one common character line is false.
```

```text
[POSITIVE]
The maximal local-to-pair object is a face-separated character fan: each selected face carries
its full integral ray `(5)`, while rationally independent rays meet only at the neutral sector.
Resonant overlaps, when present, are controlled by the integral commensurability lattice of the
period source.
```

This is the first exact gluing law for the corrected typed receiver.  It changes the open global
problem from identifying local generators to constructing the incidence and localization maps of
their face fan.

## 4. Lean certificate

`formal/GaloisForLFunctions/HTGeometry/NodalChargeCharacterRealization.lean` proves:

- `nodalChargeFrequency_mul_period`;
- `exp_nodalChargeFrequency_mul_period`;
- `nodalChargeFrequency_neg`;
- `nodalChargeFrequency_injective`;
- `nodalChargeMode_neg_mul`;
- `nodalChargeMode_add`;
- `nodalChargeMode_periodic`;
- `nodalChargeModes_linearIndependent`;
- `addTranslationMeroEquiv_nodalChargeMero`;
- `addTranslationMeroEquiv_nodalChargeMero_selected`;
- `nodalChargeMero_deriv`;
- `nodalChargeFrequency_pair_eq_iff_neutral`.

The certificate is unconditional and contains no `sorry`, `admit`, project axiom, opaque
postulate, unsafe declaration, or numerical computation.  Its dependencies were already cached;
the leaf file passed direct `lake env lean` verification and no build was run.

## 5. Novelty and anti-theatre gate

The proof uses standard facts: exponential characters, distinct-exponent linear independence,
eigenvectors of translation and differentiation, and rational independence of periods.  Toric and
logarithmic geometry already organize character lattices by boundary fans, and equivariant
K-theory already supplies localization on toric strata.  The theorem is therefore a bridge and not
new scientific knowledge.  Primary parent checks include Iwanari's logarithmic construction of
toric algebraic stacks (`arXiv:0707.2568`) and Coates--Iritani--Jiang--Segal on equivariant
K-theoretic localization for toric Deligne--Mumford stacks (`arXiv:1410.0027`).

The result nevertheless removes two false targets: one character fibre does not carry all
charges, and distinct incommensurate face fibres must not be globally identified.  Merely naming
the resulting diagram a fan, cosheaf, or constructible object would still be parent packaging.

The candidate-new theorem must construct, from an actual source--observation double with a
source-minimal HT degeneration and genuinely transverse reporter, a presentation-invariant
DA-filtered face-poset object whose:

1. stalk on face `j` is `(5)`;
2. overlap is the exact resonance sublattice, giving `(8)` in the independent case;
3. localization boundary sends the analytic Tate class `[E^m]` to the oriented interval of stalk
   generators with charges `0,...,m-1`; the charge-`m` generator is its endpoint, not its boundary;
4. coherent realization recovers the source-face `Tor` class;
5. integral and hermitian realizations preserve primitivity and orientation;
6. analytic completion remains conservative after quotienting the DA gauge.

Until that construction and its presentation invariance are proved, there is no claim of a new
unified field theory.

## Gates

- [x] reject the single-fibre realization of all nodal charges
- [x] construct every charge frequency and source character
- [x] prove selected-period annihilation and complementary-phase retention
- [x] prove arbitrary finite distinct-charge independence
- [x] construct the genuine meromorphic eigenvectors
- [x] prove rationally independent face spectra intersect only neutrally
- [ ] construct the face-poset incidence object for the actual multiple-gamma degeneration
- [ ] identify its integral localization boundary with the Tate-theta family
- [ ] compare its coherent realization with the Barnes source-face `Tor` module
- [ ] prove DA-relative and source-presentation invariance

## Lean formalization — COMPLETE (audited 2026-08-21)

`formal/GaloisForLFunctions/HTGeometry/NodalChargeCharacterRealization.lean` is wired into
`GaloisForLFunctions.HTGeometry` and re-audited: all twelve declarations listed in §4, plus
`nodalChargeFrequency_zero`, `nodalChargeMero_ne_zero`,
`nodalChargeBoundaryIntervalPairing_eq` and `nodalChargeBoundaryIntervalPairing_eq_endpoint_iff`,
depend on exactly `propext, Classical.choice, Quot.sound`. No `sorry`, `admit`, project axiom,
`opaque`, or `unsafe` declaration occurs in the file.

Correspondence with the stated theorem:

| Card equation | Lean declaration |
|---|---|
| `(1)` `λ_{j,m} = 2πi m/ω_j` | `nodalChargeFrequency`, `nodalChargeFrequency_mul_period` |
| `(2)` `χ_{j,m}(T_k) = exp(λ_{j,m} ω_k)` | `nodalChargeMode_add`, `addTranslationMeroEquiv_nodalChargeMero` |
| `(3)` the mode `ℓ_{j,m}` | `nodalChargeMode`, `nodalChargeMero` |
| `(4)` translation / differentiation / selected annihilator | `nodalChargeMode_add`, `nodalChargeMero_deriv`, `nodalChargeMode_periodic`, `addTranslationMeroEquiv_nodalChargeMero_selected` |
| `(5)`–`(6)` the charge grading is a genuine direct sum | `nodalChargeModes_linearIndependent` (with `nodalChargeFrequency_injective`) |
| `(6+)` exact charge reversal | `nodalChargeFrequency_neg`, `nodalChargeMode_neg_mul` |
| `(7)`–`(8)` face separation | `nodalChargeFrequency_pair_eq_iff_neutral` |
| the oriented charge interval and its endpoint no-go | `nodalChargeBoundaryIntervalPairing_eq`, `nodalChargeBoundaryIntervalPairing_eq_endpoint_iff` |

The six items listed at the end of §5 belong to the **candidate-new** presentation-invariant
construction, which the card states explicitly is not claimed here; they are outside the theorem
that this card banks.
