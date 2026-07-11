# Prime-translation theta defect with unitary semisimplification

- **ID:** `prime-translation-theta-unitary-defect-conjecture`
- **Stage:** 5-failed
- **Type:** TERMINAL CONJECTURE RECORD; Route A from the external verdict
- **Scientific status:** `[CLOSED IN THIS FORM]`; the required faithful comparison is RH-equivalent
- **Source:** Riemann's theta convolution, prime logarithmic translations, and the off-unitary
  Koszul contraction theorem
- **Statement:** `[CONJECTURE]` The source-defined analytic cokernel of theta convolution admits a
  canonical positive semisimplification on which the prime logarithmic translations act unitarily.
  This would force every Xi defect character onto the real spectral axis and prove RH.

## Source-first defect

Let `Phi` be the completed Riemann theta source with

```text
Fourier(Phi)(z)=XiC(z)=xi(1/2+i z).
```

Choose a translation-stable nuclear test space `E` on which convolution by `Phi` is continuous and
whose Fourier transform is an analytic function space with continuous zero jets.  Define the
two-term source complex

```text
M_Phi=[E --C_Phi--> E].                                (1)
```

No zero is used in (1).  Fourier transform identifies its analytic cokernel with multiplication by
`XiC`, so its support and local lengths are exactly the Xi divisor and its multiplicities.

Real translation by `log p` gives the prime action.  At a zero `rho`, the semisimple defect
character is

```text
p |-> exp(-i rho log p)=p^(-i rho).                    (2)
```

Its modulus is one for every prime exactly when `rho` is real, equivalently when the corresponding
zeta zero lies on `Re(s)=1/2`.

## Independent selector

The theorem
`prime-translation-koszul-off-unitary-contractibility.md` proves that the Koszul complex of the
unitary prime translations against the character (2) is quantitatively contractible whenever
`Im(rho)!=0`.  Thus a defect object which is simultaneously

```text
faithful to the analytic cokernel
and
positive/unitary for the prime translations                         (3)
```

cannot contain an off-line zero.

This is direct off-unitary coercivity, not a finite-stage support-locus argument and not a derived
limit of acyclic fibers.

## Exact open core

Construct, from `Phi` and the prime translation action before reading the divisor, a functor

```text
U : semisimple analytic cohomology of M_Phi
      -> positive Hilbert prime modules               (4)
```

such that:

1. `U` is faithful on every nonzero local support fiber;
2. the prime translations act unitarily on `U`;
3. the construction is invariant under admissible theta presentations and prime exhaustions;
4. only the semisimple support is Hilbertized, so multiple zeros are not accidentally ruled out by
   demanding a unitary nilpotent jet; and
5. the norm is obtained from a source Green, residue, or boundary form rather than declared on the
   zero fibers.

If (4) exists, an off-line zero produces a nonzero Hilbert vector with a nonunitary prime character,
contradicting (2)--(3).  Hence (4) proves RH.

The subsequent comparison theorem proves that the canonical candidate for (4), restriction to the
positive real-boundary defect, has exactly the off-real divisor as kernel.  Thus faithfulness is
equivalent to RH and is not supplied by the theta-convolution construction.  This card is retired;
the full disposition is in `route-a-prime-theta-progeometric-terminal-verdict.md`.

## The category trilemma

The paper theorem `theta-convolution-hilbert-analytic-defect-trilemma.md` blocks the two automatic
choices:

- in `L2`, the theta convolution has dense nonclosed range and zero reduced cokernel, so there is no
  defect to Hilbertize;
- in the analytic category, the cokernel sees every complex zero, but nonunitary characters are
  allowed;
- making the analytic support faithfully positive is precisely the new theorem.

The route therefore cannot claim that positivity of the physical kernel descends automatically.
Convolution by `Phi` is not a positive operator merely because `Phi(u)>0` pointwise.

## Candidate source form

`[CONJECTURE]` The only plausible noncircular form is a renormalized Green boundary form on the
nonclosed-range defect of

```text
E subset L2(R) subset E'.                              (5)
```

It must pair analytic defect functionals through finite theta energy while discarding the
nilpotent jet direction.  A useful target is a form `G_Phi` satisfying

```text
G_Phi(T_a c,T_a c)=G_Phi(c,c),
G_Phi(c,c)>0 for every nonzero semisimple defect c,      (6)
```

where `T_a` is real translation.  Equation (6) would make every defect character unitary.

No such form is currently constructed.  A residue formula that evaluates `rho` first is circular;
an `L2` quotient form is zero; and an indefinite Green form permits reciprocal off-line pairs.

The paper theorem
`translation-invariant-defect-form-orbit-classification.md` makes the last alternative exact.  Any
nondegenerate translation-invariant Hermitian form is hyperbolic on a nonreal pair, with one positive
and one negative direction.  Thus its negative index is an exact off-real-orbit counter.

## Canonical real spectral boundary

The theorem
`xi-logderivative-real-boundary-divisor-measure.md` constructs a source-defined positive form on the
**real** part of the defect with all multiplicities included.  The boundary measures

```text
d nu_epsilon(t)
  =-(1/pi) Im(XiC'(t+i epsilon)/XiC(t+i epsilon)) dt     (7)
```

converge locally in distributions to

```text
nu_Xi
  =sum_(gamma in R, XiC(gamma)=0)
       ord_gamma(XiC) delta_gamma.                      (8)
```

Equation (8) is obtained from the real theta multiplier and does not enumerate the zeros in its
definition.  On finitely supported semisimple real-zero data it yields the positive
translation-invariant norm

```text
||f||_real^2
  =sum_gamma ord_gamma(XiC)|f(gamma)|^2.                (9)
```

Nilpotent multiplicity jets are kept outside this Hilbert semisimplification.

The decisive missing theorem is now **exhaustion**, not positivity:

```text
[OPEN CORE: REAL-BOUNDARY EXHAUSTION]

Every nonzero semisimple analytic defect of M_Phi
is detected by the real spectral boundary (8).          (10)
```

An off-real zero gives an analytic defect character but contributes nothing to (8), so (10) is
equivalent to real support.  The point of (7)--(10) is to identify the exact source object and the
exact comparison map which must be proved, rather than postulate a Hilbert norm on zero fibers.

## Fake rejection

1. **Generic positive kernel.** Let `g(u)=exp(-cosh u)` and convolve it with the positive even atomic
   measure supported at `+/-a,+/-2a` with weights `1,c`, where `0<c<1`.  Its bilateral transform has
   the factor

   ```text
   cosh(a z)+c cosh(2a z),
   ```

   which has off-axis zeros because the negative root of
   `2c y^2+y-c=0` lies below `-1`.  The resulting kernel is smooth, strictly positive, even, and
   double-exponentially decreasing.  Therefore these shape properties cannot imply (6).
2. **Shifted completed product.** `xi(s+a)xi(s-a)` is a mixed-weight direct sum.  A valid purity
   theorem must reject its two radial weights before reading zeros; generic self-duality does not.
3. **Helson twist.** A unimodular prime phase twist preserves the radial character test.  The exact
   theta source, not prime unitarity alone, must prevent its prescribed off-line divisor from
   acquiring (6).
4. **Full-jet positivity.** Unitary Hilbertization of multiplicity jets forces simplicity.  The RH
   route may Hilbertize only the semisimplification unless it explicitly proves the stronger claim.
5. **Mean-square declaration.** Off-real exponentials fail the translation mean-square norm, but
   declaring the defect to live in that norm already discards off-line zeros.  Source finite energy
   must be proved.

## Immediate attacks

1. Use the exact Fourier-side category `O(C)` and its multiplier cokernel; the theorem
   `entire-multiplier-translation-defect-universality.md` proves the divisor statement there.
2. Compute the Green boundary pairing arising from the dense nonclosed `L2` range without taking a
   reduced quotient.
3. Construct the comparison map from analytic semisimple cohomology to the real spectral completion
   (7)--(9).
4. Test the same construction on the smooth positive fake above and on shifted Xi.  Any form that
   remains positive there is not zeta-specific.
5. Attack injectivity of the comparison map.  Retire Route A if injectivity is merely the assertion
   that no off-real analytic fiber exists.

## Lean surface

The formal tree already contains the theta source, its critical Fourier trace, prime dilation
unitaries, and signed Green-form algebra.  The missing object is a nuclear/rigged convolution
cokernel and its boundary form, not an elementary Lean selector.  No wrapper and no full build are
appropriate before the paper category and form are fixed.

## Gates

- [x] source-first analytic defect complex specified
- [x] determinant/support identity reduced to theta Fourier transform
- [x] off-unitary prime Koszul selector proved
- [x] Hilbert--analytic category trilemma proved
- [x] all invariant Hermitian forms classified orbit-by-orbit
- [x] canonical multiplicity-safe positive real spectral boundary constructed
- [x] shifted, Helson, generic-positive, and multiplicity fakes stated
- [x] exact analytic Frechet category and division theorem
- [x] multiplicity-safe real-boundary Green form
- [x] real-boundary comparison kernel computed
- [x] faithful positive semisimplification proved RH-equivalent, not constructed
- [ ] RH composition
- [ ] unconditional Lean formalization
