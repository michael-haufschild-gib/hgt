# The exact CCM Evans Gram splits into even and odd boundary sectors

> **2026-07-22 domain correction.** The parity split remains valid for the raw `L2` Evans map, but
> that map is not alone RH-equivalent. Completed derivative zero modes require a regularity lift
> or the completion-safe square Evans determinant; see
> `suzuki-completed-zero-mode-corona-seam-law.md`.

- **ID:** `ccm-parity-split-evans-gram-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** reflection symmetry and
  `ccm-rational-residual-finite-evans-matrix-law.md`

## Statement

Fix an aperture with characteristic degree `d_a=2L_a`. Reflection `Jf(x)=f(-x)` preserves the
exact symbol, its zero-free factor, the logarithmic Dirichlet realization, the screw operator, and
the rational residual. Hence

```text
F_a=F_a^+ direct_sum F_a^-,
R_(L_a)=R_(L_a)^+ direct_sum R_(L_a)^-,
dim F_a^+=dim F_a^-=L_a,
dim R_(L_a)^+=dim R_(L_a)^-=L_a.                         (1)
```

The exact Evans map decomposes orthogonally as

```text
M_a=M_a^+ direct_sum M_a^-,                              (2)

M_a^+:F_a^+ -> R_(L_a)^+ direct_sum C_mean direct_sum C_const,
M_a^-:F_a^- -> R_(L_a)^- direct_sum C_slope.             (3)
```

Here `C_const` is the value of the affine function `G_au` at zero, while `C_slope` may be read as
its value at `a/2` after the zero value is forced by oddness. Consequently

```text
det(M_a^*M_a)
 =det((M_a^+)^*M_a^+) det((M_a^-)^*M_a^-),              (4)
```

and

```text
ker G_a={0}
 iff M_a^+ and M_a^- are both injective.                 (5)
```

Thus the three-dimensional excess target of the rectangular Evans map is canonically graded as

```text
two even channels: mean and affine constant,
one odd channel: affine slope.                            (6)
```

## Proof

The corrected symbol `W_a` is even. Its real zeros occur in opposite pairs, and the characteristic
ODE has equal even and odd solution dimensions `L_a`. The normalized factors `b_a,c_a` are even,
so their Fourier multipliers commute with reflection. The supported logarithmic form and its
Dirichlet inverse also commute with reflection by uniqueness. Therefore `f`, `u_f`, `v(f)`, and the
rational residual all retain the same parity.

The residual space in the basis

```text
x^j exp(x), x^j exp(-x),       0<=j<L_a                   (7)
```

is reflection invariant. Its even and odd eigenspaces each have dimension `L_a`, proving `(1)`.

For odd `u`, the mean vanishes. Since the screw kernel is even, `G_au` is odd; if the differentiated
null equation makes it affine, its constant term and its value at zero vanish automatically, and
the value at `a/2` detects the remaining slope. For even `u`, `G_au` is even; an even affine
function is constant, so the two original point anchors are equivalent to the single value at zero,
while the mean remains an independent condition. This proves `(2)`--`(3)` and `(6)`.

With reflection-invariant Hermitian metrics, the two target sectors are orthogonal. The Gram matrix
is block diagonal, giving `(4)`. Kernel decomposition gives `(5)`. `QED`

## Positive CCM consequence

The RH-bearing determinant theorem separates exactly into

```text
even theorem:
  residual + mean + constant anchor is injective,

odd theorem:
  residual + slope anchor is injective.                  (8)
```

Any source orientation or determinant-line lift must respect this grading. The actual cokernel is
not yet identified with these target lines, but the rectangular presentation's excess channels are
the canonical FE/Schwarz boundary package `(2 even)+(1 odd)`. This is the natural target for a
parity-preserving comparison with Suzuki's two self-adjoint extension sectors and with the even/odd
Sonin polarizations.

## Scope and classification

Parity decomposition and block-Gram factorization are standard. The theorem is route
infrastructure, not new scientific knowledge. Its finite-dimensional shadow would be wrapper-only
Lean work; the substantive analytic maps are not formalized, so no Lean file is added.

## Gates

- [x] characteristic and residual spaces split into equal parity dimensions
- [x] Dirichlet reconstruction proved parity-preserving
- [x] three anchor channels graded as two even plus one odd
- [x] Evans Gram determinant factored by parity
- [ ] prove injectivity in the even sector for every aperture
- [ ] prove injectivity in the odd sector for every aperture
- [ ] RH
