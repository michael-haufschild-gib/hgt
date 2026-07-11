# Route A prime--theta pro-geometric terminal verdict

- **ID:** `route-a-prime-theta-progeometric-terminal-verdict`
- **Stage:** 5-failed
- **Type:** TERMINAL RH ROUTE VERDICT
- **Scientific status:** `[PROVED ROUTE CLASSIFICATION; RH NOT PROVED]`
- **Scope:** Route A from the external mathematical verdict: source-first determinant, singular
  category, and finite-character or off-unitary coercivity
- **Statement:** The route admits a valid off-unitary prime selector and a canonical source-first
  theta defect, but the only canonical positive boundary sees the real sub-divisor.  The comparison
  from the full analytic defect to that boundary has precisely the off-real divisor as kernel, so
  the required exhaustion theorem is equivalent to RH.  No independent prime--theta theorem closes
  it.

## What was repaired

The invalid mechanism

```text
acyclic finite specialized complexes
  -> R^1 lim cohomology
```

was removed.  A derived inverse limit of zero objects is zero.  The legitimate singular object is
instead the analytic theta-convolution cokernel, or a separately specified nonclosed-range or
base-change defect.

The naive heat-plus-particle joint algebra was also removed: one heat aperture together with the
particle diagonal generates `B(l2(N))` and destroys the former normal superselection center.

## What Route A genuinely constructs

1. **Off-unitary prime selector.**  For the unitary logarithmic prime translations and
   `delta_s(p)=p^(1/2-s)`, the Koszul complex is quantitatively contractible off the critical line.
2. **Source-first analytic divisor.**  Convolution by Riemann's theta source has Fourier multiplier
   `XiC`.  In the explicit Frechet category `O(C)`, its multiplier cokernel has exactly the full Xi
   divisor with multiplicities.
3. **Category classification.**  The reduced `L2` cokernel is zero, while the analytic cokernel
   admits nonunitary off-real characters.
4. **Invariant-form classification.**  Every nonreal conjugate pair is a hyperbolic plane in any
   nondegenerate translation-invariant Hermitian form.
5. **Positive real defect.**  The boundary jump of `XiC'/XiC` gives the canonical positive atomic
   measure on all real Xi zeros, with multiplicities.

These are complete paper theorems recorded separately in stage 2.

The theorem `entire-multiplier-translation-defect-universality.md` also removes category ambiguity:
the full analytic construction is rigorous, but it works unchanged for every nonzero entire
multiplier.  The prime-logarithm translation action is therefore divisor-universal and supplies no
zeta-specific localization by itself.

## Exact terminal obstruction

Let

```text
D_an  = semisimple analytic theta defect,
D_real= positive logarithmic-derivative boundary defect.
```

The canonical comparison is restriction to the real spectral axis.  The theorem
`theta-analytic-to-real-defect-kernel-is-offreal-divisor.md` proves

```text
ker(D_an -> D_real)
  = the full off-real Xi divisor.                       (1)
```

Therefore

```text
D_an -> D_real is faithful
  iff RH.                                               (2)
```

The proposed positive semisimplification is not a consequence of the constructed source objects.
It is exactly the assertion that (1) vanishes.

## Why the remaining assertion is not supplied by generic structure

- Smooth, strictly positive, even, double-exponentially decreasing kernels can have off-axis
  Fourier--Laplace zeros.
- Functional-equation self-duality accepts reciprocal off-line pairs.
- Shifted products `xi(s+a)xi(s-a)` have Euler and Gamma data with mixed radial weights and off-line
  divisors.
- Helson twists preserve the prime Hilbert wall while allowing prescribed continued divisors.
- An indefinite Green form naturally accommodates every off-line pair as a hyperbolic block.
- Requiring the analytic defect to have finite translation mean-square discards off-real characters
  by definition rather than by a source theorem.
- The exact analytic multiplier complex, prime action, and off-unitary contraction exist for every
  entire function, including real entire functions with nonreal conjugate zeros.

Thus neither theta positivity, prime unitarity, symmetry, geometric-origin language, nor the chosen
singular category proves (2).

## Final disposition

`[CLOSED IN THE CONSTRUCTED FORM]` Route A succeeds as a classification:

```text
off-line Xi orbits
  = negative hyperbolic sectors
  = kernel of analytic-to-real boundary comparison.
```

It does not prove that this sector is absent.  Reopening Route A requires an actually constructed
non-scalar prime--theta object with a pre-divisor purity or coercivity theorem that implies
faithfulness of the comparison.  Merely postulating such an object or calling faithfulness
"polarization" is RH in new notation.

## Lean disposition

No full Lean build was run.  The elementary unitary resolvent selector could be formalized, but it
does not advance the missing source theorem.  The analytic-to-real kernel statement is a
tautological divisor projection and should not receive wrapper formalization.

## Gates

- [x] invalid derived-limit mechanism removed
- [x] naive joint-algebra extension removed
- [x] off-unitary prime Koszul selector proved
- [x] source-first analytic theta defect constructed
- [x] invariant forms classified
- [x] positive multiplicity-safe real boundary constructed
- [x] comparison kernel identified with off-real divisor
- [x] remaining faithfulness proved equivalent to RH
- [x] route closed in its constructed form
