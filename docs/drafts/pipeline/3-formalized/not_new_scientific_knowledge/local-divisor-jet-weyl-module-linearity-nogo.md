# Local divisor-jet Weyl module-linearity no-go

- **ID:** `local-divisor-jet-weyl-module-linearity-nogo`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (paper + Lean), `[PROVED]`, `[BRIDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/LocalDivisorJetWeylNoGo.lean`
- **Route:** `../../1-in-progress/dyadic-weld-weyl-multiplicity-route.md`

## Theorem

Let `A` be a commutative semiring.  Every `A`-linear endomorphism of the rank-one module `A` is
multiplication by its value at `1`.  Consequently

```text
End_A(A)
```

is commutative.  If invertible `A`-linear maps `U,V` satisfy

```text
U V = zeta V U,
```

then `zeta=1`.

For the local divisor-jet algebra

```text
A_m = C[X]/(X^m),
```

constant jets are injective when `m>0`.  Hence at every positive dyadic depth `k`, no pair of
invertible `A_m`-linear endomorphisms realizes the nontrivial phase

```text
Bottcher.dyadicRoot(k).
```

## Proof

For `F in End_A(A)`, `A`-linearity gives

```text
F(x)=F(x*1)=x F(1).
```

Thus `U(V(x))=x V(1)U(1)=x U(1)V(1)=V(U(x))`.  If the maps are invertible, their product sends
`1` to a unit.  Comparing the commuting identity with the projective identity and cancelling that
unit gives `zeta=1`.  The coefficient-zero characterization of `C[X]/(X^m)` proves injectivity of
constant jets.  A primitive root of order `2^k>1` is not one.

## Positive statement from the no-go

The internal Weyl generators cannot both preserve the complete local divisor-jet module structure.
This removes an overstrong compatibility clause from the live route.

The smallest viable successor is semilinear:

```text
A_m = C[X]/(X^m),
sigma_zeta(X)=zeta X,
sigma_zeta M_X = zeta M_X sigma_zeta.
```

In other words, the correct local category is a skew or crossed product

```text
A_m rtimes <sigma_zeta>,
```

not `End_(A_m)(A_m)`.  A source-derived Weyl action must twist the local coordinate or local
presentation; ordinary module endomorphisms are structurally too commutative.

## Formal surface

- `moduleEnd_self_commute`
- `localDivisorJet_moduleEnd_commute`
- `constLocalDivisorJet_injective`
- `phase_eq_one_of_moduleEnd_weyl`
- `moduleLinearEquiv_apply_one_isUnit`
- `phase_eq_one_of_moduleLinearEquiv_weyl`
- `localDivisorJet_phase_eq_one_of_moduleEnd_weyl`
- `no_dyadic_localDivisorJet_moduleLinearEquiv_weyl`

## Verification

`lake env lean GaloisForLFunctions/RHTower/LocalDivisorJetWeylNoGo.lean` passes on the repository
toolchain.

## Novelty and significance gate

This is standard rank-one module theory.  No claim of new scientific knowledge is made.  Its
research value is the exact category correction: the live local action must be semilinear rather
than linear over the full divisor-jet algebra.

## Gates

- [x] 0 -> 1: local-module compatibility failure stated
- [x] 1 -> 2: commutant and phase-one theorem proved
- [x] 2 -> 3: local dyadic specialization formalized and checked
- [ ] 3 -> 4: not promoted; construction of the source semilinear action remains open
