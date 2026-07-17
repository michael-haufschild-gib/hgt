# Scaled L1 periodization reads exact Euclidean Fourier samples

- **ID:** `scaled-l1-periodization-fourier-coefficient-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / POISSON--MUNTZ INFRASTRUCTURE
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Statement:** Every integrable complex function has a scaled integer periodization whose
  `m`-th unit-cell Fourier coefficient is exactly `a` times its Euclidean Fourier transform at
  `a*m`.

## Exact theorem

Let `f` be integrable on the real line and let `a>0`. Define

```text
P_(f,a)(x)=sum_(k in Z) f((x+k)/a).
```

The series is absolutely convergent for almost every `x` in a unit cell. For every integer `m`,

```text
integral_(0,1] exp(-2*pi*i*m*x) P_(f,a)(x) dx
  =a * Fourier(f)(a*m),                                      (1)
```

with the Fourier convention

```text
Fourier(f)(w)=integral_R exp(-2*pi*i*x*w) f(x) dx.
```

## Complete proof

Put `f_a(x)=f(x/a)`. Since `a` is nonzero and `f` is integrable, change of variables under the
linear homeomorphism `x |-> x/a` shows that `f_a` is integrable. The unscaled L1-periodization
coefficient theorem therefore gives

```text
integral_(0,1] exp(-2*pi*i*m*x) sum_(k in Z) f_a(x+k) dx
  =Fourier(f_a)(m).                                           (2)
```

The series in `(2)` is exactly `P_(f,a)(x)`. It remains only to scale the Fourier transform. By
the definition of the Fourier transform and the substitution `x=a*y`,

```text
Fourier(f_a)(w)
 =integral_R exp(-2*pi*i*x*w) f(x/a) dx
 =a * integral_R exp(-2*pi*i*y*(a*w)) f(y) dy
 =a * Fourier(f)(a*w).                                        (3)
```

The absolute Jacobian is `|a|=a` because `a>0`. Both integrals are legitimate: multiplication by
the unit-modulus Fourier character preserves integrability, and composition with division by a
nonzero scalar preserves integrability. Substituting `w=m` in `(3)` and then using `(2)` proves
`(1)`. No pointwise convergence of the periodization and no Poisson summation hypothesis is used.

## Route role

Equation `(1)` is the exact scale-matching step needed to turn the Abel boundary theorem for a
compact periodized source into sampled values `Fourier(f)(a*m)`. Evenness and zero mean can then
separate the bilateral coefficient identity into the one-sided Poisson--Muntz formula. This theorem
is classical infrastructure; it is not the candidate-new source estimate.

