# Dual Hecke theta unfolding over fractional-ideal classes

- **ID:** hecke-dual-theta-unfolding-over-fractional-ideal-classes
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Primitive Gauss and dual-character arithmetic](hecke-primitive-gauss-sums-and-arithmetic-dual-character.md)
- **Statement:** The actual dual unit-averaged Mellin transform is the inverse-character class series with exact arithmetic and analytic factors; its finite class recombination gives the primitive completed functional equation.

## Fractional class and unit orbits

Let `J_b=dual(mb)`. For each integral ideal `I` in class `[J_b]^-1`,
choose a generator `g_I` of the actual principal product `I J_b`.
The map `(I,u) ↦ u*g_I` is a bijection onto the nonzero elements of `J_b`.
Equality of principal fractional ideals supplies the global unit for
surjectivity; cancellation proves injectivity. Fractional norms give

```
|Norm(g_I)| = Norm(I) Norm(J_b),
Norm(J_b) = (|disc K| Norm(m) Norm(b))^-1.
```

The identity `J_b*b=J_1` identifies the inverse dual class as
`[J_1]^-1[b]`. Since the chosen base for `c` has class `c^-1`, the actual
dual classes are indexed by the permutation `c ↦ [J_1]^-1 c^-1`.

- [Fractional class/unit orbits](fractional-ideal-elements-are-class-unit-orbits.md)
- [Trace-dual norms](number-field-trace-duals-have-discriminant-norms.md)
- [Actual dual generators and permutation](hecke-dual-frequencies-have-class-generators.md)

## Absolute unit unfolding

The actual dual average uses the negative weighted logarithmic profile.
Its kernel at `u*a` is the kernel at `a` translated by `x+log(u)`;
finite Fourier and infinite sign factors cancel on actual global units.
An injection from class/lattice pairs into actual dual frequencies pulls
back the proved uniform Gaussian majorant to one summable bound on the
unit domain.

Positive-translation fundamental-domain unfolding first proves
whole-space integrability and summability of absolute masses. Complex
unfolding then applies. Torsion independence contributes its exact order,
unit-domain volume contributes the regulator, and Haar negation yields

```
dualAverage(t) - regulator*dualZeroMode
  = torsionOrder * sum_I integral_whole_log
      F_b(g_I)*parityKernel(psi,weightedProfile(x),t,g_I).
```

- [Actual unit covariance](hecke-dual-theta-kernels-are-unit-covariant.md)
- [Absolute family unfolding](number-field-log-periodizations-have-absolute-unfolding.md)
- [Actual dual unit unfolding](hecke-dual-unit-orbits-unfold-over-the-log-space.md)

## Exact Mellin exchange

For every nonzero field element, the actual parity kernel has the exact
Gamma/Jacobian Mellin integral and translated absolute norm mass. The
proved inverse-character Fourier coefficient gives

```
A_b(s) = C_psi psi(b) Norm(J_b)^(-s),
density_I = idealTerm(psi^-1,s,I) A_b(s)
              * archimedeanKernel(s,radialLog(p)+logProfile(g_I)).
```

Absolute ideal-series convergence makes the joint norm masses summable
on `Re(s)>1`. Fubini bounds radial masses by joint masses, justifying the
infinite Mellin exchange after `t=exp(2q)`. Thus

```
Mellin(dualAverage-regulator*dualZeroMode)(MArg_psi(s))
  = torsionOrder * inverseCharacterClassSeries(s) * A_b(s)
      * Gamma_psi(s)/(degree * 2^unitRank).
```

For zero parity, the symmetric weak theta pair gives this Mellin value
on the same half-plane. For nonzero parity, its actual zero modes vanish,
so the symmetric strong pair gives the identity. Inversion invariance
identifies the inverse character's Gamma factor.

- [Field-element Mellin integrals](hecke-field-element-kernels-have-exact-mellin-integrals.md)
- [Exact dual class integrals](hecke-dual-class-kernels-have-exact-mellin-integrals.md)
- [Actual averaged Mellin identity](hecke-dual-averaged-mellin-is-the-inverse-class-series.md)
- [Inversion invariance](hecke-conductors-and-parities-are-invariant-under-inversion.md)

## Arithmetic normalization and global reflection

Write `D=|disc K|`, `N=Norm(m)`, `B=Norm(b)`, `delta=D*N`, and let `d`
be the real parity degree. The reflected factors are

```
weight_b(1-s) = psi(b)^-1 B^(1-s),
PoissonScalar_b = (-i)^d/(N B sqrt(D)),
A_b(s) = C_psi psi(b) (delta B)^s.
```

Their product is independent of the base ideal:
`C_psi (-i)^d delta^s/(N sqrt(D))`. Multiplication by
`delta^((1-s)/2)` gives `W_psi delta^(s/2)`, where
`W_psi=(C_psi/sqrt(N))(-i)^d` has absolute value one.

Raw completed residues cancel for nontrivial characters by ordinary-class
orthogonality and nonvanishing Gamma at one. Entire divided differences
fill their removable values. The dual class permutation now recombines
the actual Mellin series into the full inverse-character L-function.
This proves completed reflection on `Re(s)>1`.

Define the pole-cleared entire function from its regular part and
constant residues before totalized division. Analytic uniqueness gives
global reflection for this function, and hence completed reflection away
from zero and one. For nontrivial characters, entireness gives completed
reflection at every point, including both removable values.

- [Raw residue cancellation](hecke-completed-theta-residues-cancel.md)
- [Completed removable values](hecke-gamma-completed-functions-have-removable-values.md)
- [Exact arithmetic normalization](hecke-completion-factors-have-exact-arithmetic-normalization.md)
- [Primitive completed functional equation](primitive-hecke-l-functions-have-completed-functional-equation.md)

## Verification and closure

All statements above are formalized. Each module's final direct source
audit passes without warnings; every recorded main transitive axiom
audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
Finished modules are wired into their umbrellas without compiling them.
Only consumer-required dependency oleans were built. The final functional-equation module needs no consumer olean.

The existing drafts and paper proofs are closed, with no unchecked
scratch proof remaining. HL7 is complete. The larger programme remains
paused before class field theory, as requested.
