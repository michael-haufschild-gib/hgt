# Gamma's analytic and algebraic jet realizations have opposite boundary variance

- **ID:** `gamma-opposite-variance-boundary-channels`
- **Stage:** 3-formalized
- **Type:** GAMMA COMPARISON MODEL / EXACT BOUNDARY CHANNELS
- **Scientific status:** `[LEAN-FORMALIZED] [EXACT MODEL THEOREM] [PARENT ALGEBRA]`
- **Parent:** `../1-in-progress/gamma-opposite-variance-weyl-seam.md`
- **Statement:** Finite Taylor translation is forward-compatible with an outgoing truncation
  defect, whereas coordinate-multiplication prolongation is truncation-compatible with an incoming
  extension defect. The two realizations expose opposite one-boundary channels of Gamma's shift
  equation.

## Exact analytic channel

On raw jets, finite Taylor translation satisfies

```text
E_(N+1)i_N=i_N E_N,                                       (1)
p_N E_(N+1)-E_N p_N=beta_N b_N,                           (2)
beta_N(1)=(1/N!,1/(N-1)!,...,1).                          (3)
```

Thus translation is Ind-flat and Pro-curved, with an outgoing channel from the new highest
derivative into all retained Taylor observables.

## Exact algebraic channel

Differentiating multiplication by `z` gives

```text
(Z_N(z)a)_j=z a_j+j a_(j-1).                              (4)
```

The Lean-formalized adjacent-clock laws are

```text
p_N Z_(N+1)(z)=Z_N(z)p_N,                                 (5)
(Z_(N+1)(z)i_N-i_N Z_N(z))(a)|old=0,                      (6)
(Z_(N+1)(z)i_N-i_N Z_N(z))(a)|new=N a_(N-1).              (7)
```

Thus coordinate multiplication is Pro-flat and Ind-curved, with an incoming channel from the old
highest derivative into the new boundary slot.

## Lean declarations

`GaloisForLFunctions.HTGeometry.GammaPeriodicConstraintCorona` contains:

- `gammaClockCoordinateMultiplication`;
- `gammaClockCoordinateMultiplication_truncate`;
- `gammaClockCoordinateIncoming`;
- `gammaClockCoordinateIncoming_apply_castSucc`;
- `gammaClockCoordinateIncoming_apply_last`;
- the previously formalized translation, curvature, extension, and boundary-symbol declarations.

The existing object cache was reused and the touched source passed direct Lean verification. No
build was run.

## Scientific boundary and positive theorem

The Leibniz jet matrix and its one-slot defect are elementary. They do not by themselves define a
new invariant. The positive theorem is the exact source comparison shape: the two sides of
`Gamma(z+1)=z Gamma(z)` have opposite clock variance and supply canonical incoming and outgoing
boundary channels without inserting an adjoint or external carrier.

The candidate-new result is their source-topological comparison: prove that the paired channels
form the finite boundary current of the Gamma parameterized-Galois/analytic comparison torsor.

## Gates

- [x] coordinate-multiplication jet action formalized
- [x] exact truncation compatibility formalized
- [x] exact incoming boundary support formalized
- [x] exact incoming boundary coefficient formalized
- [ ] exponentiated Weyl boundary current formalized
- [ ] paired-channel migration law formalized
- [ ] source comparison torsor constructed
