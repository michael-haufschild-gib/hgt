# Every self-adjoint BBM pullback completion remains purely continuous

- **ID:** `bbm-pullback-completion-purely-continuous-law`
- **Stage:** 2-fully-proven
- **Type:** DIRECT HILBERT--PÓLYA OPERATOR VERDICT / POSITIVE DOMAIN LAW
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Route status:** The exact Bender--Brody--Muller pullback metric and similarity cannot be repaired
  by choosing a better closed domain. A viable realization must change the metric, the closed
  intertwining relation, or the arithmetic operator itself.
- **Statement:** Complete a BBM test domain in the norm `||f||_eta=||Delta f||_2`, quotienting the
  nullspace if necessary. If the formal relation

  ```text
  Delta H=A Delta,   A=xp+px,                               (1)
  ```

  survives closure and `H` is self-adjoint, then `H` is unitarily equivalent to a reducing part of
  the ordinary dilation generator `A`. Its spectrum is purely absolutely continuous and it has no
  point eigenvalues. Therefore the boundary equation `psi_z(0)=0`, although equal to `zeta(z)=0`
  on formal Hurwitz functions, cannot produce Hilbert--Pólya point spectrum in this completion.

## 1. Abstract pullback-completion theorem

Let `K` be a Hilbert space, let `A` be self-adjoint on `K`, and let `D` be a complex vector space
with a linear map

```text
Delta:D->K.                                                 (2)
```

Give `D/ker Delta` the norm

```text
||[f]||_eta=||Delta f||_K                                  (3)
```

and let `H_eta` be its completion. The map in `(2)` extends uniquely to a unitary

```text
U:H_eta -> M,
M=closure(range Delta) subset K.                            (4)
```

Suppose a densely defined operator `T` on `H_eta` is self-adjoint and satisfies

```text
U Dom(T) subset Dom(A),
U T f=A U f,                 f in Dom(T).                   (5)
```

Then `B=U T U^(-1)` is a self-adjoint restriction of `A` to `M`.

### Reducing-subspace lemma

`[PROVED]` The closed subspace `M` reduces `A`.

Take `z in C\R`. Since `B` is self-adjoint, `B-z` maps `Dom(B)` bijectively onto `M`. For `y in M`,
let `x in Dom(B)` solve

```text
(B-z)x=y.                                                   (6)
```

Because `B` is a restriction of `A`, `(A-z)x=y`. The self-adjoint resolvent of `A` gives the unique
solution in `Dom(A)`, hence

```text
x=(A-z)^(-1)y in M.                                        (7)
```

Thus `(A-z)^(-1)M subset M`. Applying the same argument to `conj z` gives invariance under the
adjoint resolvent. Therefore `M` is a reducing subspace for `A`, and

```text
B=A restricted to M.                                       (8)
```

Every spectral measure of `B` is the restriction of a spectral measure of `A`. In particular, if
`A` is purely absolutely continuous, so is `B`. QED.

## 2. Dilation generator

On `K=L2(R_+,dx)`, take

```text
A=xp+px=-i(2x d/dx+1).                                     (9)
```

The logarithmic Jacobian unitary

```text
(Vf)(u)=exp(u/2) f(exp u),   u in R,                       (10)
```

sends `A` to the constant-coefficient momentum operator

```text
V A V^(-1)=-2i d/du                                        (11)
```

on `L2(R,du)`. The Fourier transform sends `(11)` to multiplication by `2t`. Consequently

```text
spec(A)=R,
A has purely absolutely continuous spectrum,
ker(A-lambda)=0 for every lambda in C.                      (12)
```

Applying the abstract theorem shows that every self-adjoint operator satisfying `(5)` in a
pullback completion has the same spectral type on a measurable reducing subset: it has no point
spectrum.

## 3. Application to the BBM metric

Bender, Brody, and Muller use

```text
Delta=1-exp(-ip),
H=Delta^(-1) A Delta,
eta=Delta^* Delta                                           (13)
```

up to an inessential positive scalar normalization. Their formal Hurwitz state satisfies

```text
psi_z(x)=-zeta(z,x+1),
Delta psi_z=x^(-z),
psi_z(0)=0 iff zeta(z)=0.                                   (14)
```

The companion card `../../3-formalized/not_new_scientific_knowledge/bbm-pullback-metric-no-point-spectrum.md` proves directly that `x^(-z)` is not
in `L2(R_+)` for any `z`, with the exact incompatible end conditions

```text
Re z<1/2 at zero,
Re z>1/2 at infinity.                                      (15)
```

The present theorem closes the remaining domain objection. Even if one starts with a different
test domain, quotients the nullspace of `Delta`, completes it in the exact metric `(13)`, and
assumes a self-adjoint closure exists, preservation of the claimed similarity `(1)` forces purely
continuous spectrum by `(4)`--`(12)`. A boundary condition imposed only on formal generalized
eigenfunctions cannot turn them into point eigenvectors of that closure.

## 4. Positive domain law

A successful BBM-type Hilbert--Pólya realization must violate at least one precise premise of the
pullback theorem.

1. **Non-pullback metric:** its Hilbert norm is not `||Delta f||_2`, even after quotient and
   completion.
2. **Arithmetic anomaly in the closed intertwiner:** the formal identity `Delta H=A Delta` acquires
   a nonzero closed boundary/seam term carrying the prime data.
3. **Non-reducing arithmetic coupling:** the transformed operator is `A+V_arith`, where
   `V_arith` changes the essential spectral type and is not relatively compact.
4. **Different spectral claim:** the construction is an absorption or scattering realization, not
   a discrete Hilbert--Pólya point-spectrum proof; it must then supply a separate transverse
   localization theorem.

For a direct point-spectrum proof, clauses 1--3 combine into one required object:

```text
source-selected two-ended arithmetic graph/domain
  -> closed noncompact prime coupling
  -> discrete self-adjoint spectral measure
  -> exact Xi determinant.                                  (16)
```

The finite archimedean Gamma-product boundary law shows that the archimedean part supplies only one
projective valuation direction. The noncompact term in `(16)` must therefore transport the
infinite prime-log module explicitly; at cutoff `N` its marked phase dimension is at least `pi(N)`.

## 5. Compact-perturbation consequence

The same spectral theorem gives a second positive necessity. If `K` is a bounded self-adjoint
compact operator, Weyl's theorem gives

```text
spec_ess(A+K)=spec_ess(A)=R.                                (17)
```

Thus `A+K` cannot have compact resolvent or purely discrete zeta spectrum. If the perturbation is
trace class, Kato--Rosenblum further preserves the absolutely continuous part up to unitary
equivalence. Therefore a viable arithmetic coupling is necessarily noncompact and, if bounded,
outside trace class. Finite-rank boundary corrections cannot be the cofinal spectral producer.

This does not exclude finite-rank corrections at each cutoff followed by a singular non-norm limit.
Such a family must prove its own zero-preserving limit theorem and cross the `1/log N` boundary
layer; the infinite operator is not a compact perturbation of `A` in that case.

## 6. Scope and novelty

- The theorem closes only completions retaining both the exact pullback norm and the closed
  similarity to the ordinary dilation generator.
- An unbounded, domain-changing, noncompact prime interaction remains logically viable.
- Connes absorption spectra, CCM, Sonin/prolate, and finite-Weil determinant limits are outside the
  point-spectrum verdict.
- The conclusion does not say finite-prime routes are impossible; it says their cofinal coupling
  must cease to be compact in the global operator topology.

After project notation is removed, the proof is the standard reducing-subspace resolvent argument,
Fourier diagonalization of momentum, Weyl invariance of essential spectrum, and Kato--Rosenblum.
It is therefore a useful direct Hilbert--Pólya closure theorem, not new scientific knowledge.

## References

1. C. M. Bender, D. C. Brody, M. P. Muller, *Hamiltonian for the Zeros of the Riemann Zeta
   Function*, Phys. Rev. Lett. 118 (2017), 130201.
2. T. Kato, *Perturbation Theory for Linear Operators*, Springer.
3. M. Reed, B. Simon, *Methods of Modern Mathematical Physics III: Scattering Theory*, Academic
   Press.

## Gates

- [x] pullback completion identified with a closed subspace of ordinary `L2`.
- [x] self-adjoint restriction proved reducing by resolvent uniqueness.
- [x] dilation spectral type computed by logarithmic and Fourier unitaries.
- [x] BBM point-spectrum consequence derived.
- [x] compact and trace-class repairs excluded.
- [ ] construct a noncompact source-selected arithmetic coupling satisfying `(16)`.
