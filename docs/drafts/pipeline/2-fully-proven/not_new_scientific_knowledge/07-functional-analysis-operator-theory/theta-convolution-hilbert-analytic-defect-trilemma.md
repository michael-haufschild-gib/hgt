# Theta convolution faces a Hilbert--analytic defect trilemma

- **ID:** `theta-convolution-hilbert-analytic-defect-trilemma`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); Route-A category gate
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** Riemann's theta Fourier kernel, Fourier multiplication, and finite-dimensional
  unitary representation theory
- **Statement:** The theta convolution operator has zero reduced Hilbert kernel and cokernel, so the
  Hilbert category is unitary but cannot see isolated Xi zeros.  Its analytic cokernel sees the full
  complex Xi divisor, but the translation character at a zero is unitary exactly when that zero is
  real.  Full jet unitarity additionally forces the zero to be simple.

## Source convolution

Let `Phi` be Riemann's real even theta source in logarithmic coordinates, normalized so that

```text
Fourier(Phi)(z)=XiC(z)=xi(1/2+i z).                    (1)
```

The source is rapidly decreasing, and `XiC` is entire, real on the real axis, nonzero as a
function, and tends to zero along the real axis at infinity.

On `L2(R)`, convolution by `Phi` is the bounded operator

```text
C_Phi f=Phi*f.
```

Fourier transform identifies it with multiplication by `XiC(t)` on the real line.

## Hilbert category: automatic unitarity, no divisor

Since a nonzero real-analytic function has a measure-zero real zero set,

```text
ker(C_Phi)=0.                                          (2)
```

The operator is self-adjoint, so

```text
closure(range(C_Phi))
  =(ker(C_Phi^*))^perp
  =L2(R).                                               (3)
```

Thus the reduced Hilbert cokernel is zero.

The range is not closed.  Since `XiC(t)->0`, there are unit vectors with Fourier support where
`|XiC|` is arbitrarily small.  Their images under `C_Phi` tend to zero, so the injective operator is
not bounded below; an injective bounded operator with closed range would be bounded below.

Consequently the Hilbert category has exactly the desired unitary translation action but erases
all isolated zero defects:

```text
ker=0,
L2/closure(range)=0,
range nonclosed.                                       (4)
```

## Analytic category: full divisor, no automatic unitarity

On the Fourier side consider the source-defined analytic complex

```text
O(C) --multiplication by XiC--> O(C).                   (5)
```

Its cokernel is supported exactly on the complex Xi divisor.  At a zero `rho` of multiplicity `m`,
the local primary quotient is

```text
C{z-rho}/(z-rho)^m.                                    (6)
```

Physical translation by `a in R` acts in Fourier coordinates by multiplication by

```text
exp(-i a z).                                           (7)
```

On the semisimple quotient of (6), this action has character

```text
a |-> exp(-i a rho).                                   (8)
```

The character (8) is unitary for every real `a` exactly when

```text
Im(rho)=0.                                             (9)
```

In the Xi coordinate, all zeros satisfying (9) is exactly RH.

If `m>1`, multiplication by (7) on (6) has a nontrivial unipotent Jordan part, obtained by expanding
the exponential in `z-rho`.  A finite-dimensional unitary representation is diagonalizable, so the
full jet module (6) is unitarizable only when both

```text
Im(rho)=0 and m=1.                                     (10)
```

Thus unitarity of the semisimplified analytic defect is RH, while unitarity of the complete local
jet defect implies RH plus simplicity of every zero.

## Trilemma

The canonical source models leave exactly three possibilities:

1. **Reduced Hilbert defect:** translations are unitary, but the defect is zero and no Xi zero is
   detected.
2. **Analytic or rigged defect:** every complex zero and its multiplicity is detected, but off-line
   characters and nonunitary jets are legitimate.
3. **Faithful positive defect:** a source-derived positive Hilbertization of the semisimple analytic
   cokernel would prove RH; a positive Hilbertization of the full jet cokernel would also prove
   simplicity.

Passing from item 2 to item 3 is therefore not a formal consequence of the theta convolution
presentation.  It is the localization theorem.

## Route consequence

The theorem supplies a precise singular category and a source-first divisor object, but it also
identifies the burden exactly.  A pro-geometric Route A must construct a positive/unitary
semisimplification before inspecting zeros.  Merely choosing the Hilbert quotient loses the divisor;
merely choosing the analytic quotient admits hypothetical off-line zeros.

Pointwise positivity of the physical theta kernel does not resolve the trilemma: convolution is
positive on `L2` only if its Fourier multiplier is nonnegative, whereas `XiC` changes sign across
its real zeros.

## Gates

- [x] Hilbert kernel and reduced cokernel proved zero
- [x] Hilbert range proved dense and nonclosed
- [x] analytic local defect and translation character computed
- [x] semisimple unitarity proved equivalent to real support
- [x] full jet unitarity proved to force simplicity
- [ ] no Lean formalization planned before a live positive defect construction exists
