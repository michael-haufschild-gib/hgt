# Interior seam indicial dipole exclusion

- **ID:** `suzuki-interior-seam-indicial-dipole-exclusion`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-interior-seam-indicial-dipole-exclusion.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/InteriorSeamIndicialMatrix.lean`

## Formal content

The card's decisive content is the interior indicial matrix `(3)` and its spectrum `(4)`, from
which the exclusion `(5)` follows. Lean proves all of it:

```text
orientationSwap v   = (v.2, v.1)
indicialMatrix tau v = (((1-2tau) v.1 - v.2)/(1-tau), ((1-2tau) v.2 - v.1)/(1-tau))
```

| Card | Lean |
|---|---|
| `(3)` `I_tau = [(1-2tau)I - J]/(1-tau)` | `indicialMatrix`, `indicialMatrix_apply` |
| `(4)` `lambda_sym = -2tau/(1-tau)` | `indicialMatrix_sym` |
| `(4)` `lambda_anti = 2` | `indicialMatrix_anti` |
| `(5)` bounded forcing forces `beta_+ = beta_- = 0` for `0<tau<1` | `indicialMatrix_eq_zero_iff` |
| `(6)` at `tau = 1` boundedness forces antisymmetry | `indicialNumerator_kernel_at_one` |

`indicialMatrix_eq_zero_iff` is an iff, so it records both that the matrix is injective on the
stated range and that it annihilates only the zero pair. The injectivity proof does not go through
the eigenvalues: eliminating between `(1-2tau) beta_+ = beta_-` and `(1-2tau) beta_- = beta_+`
gives `beta_+ * 4 tau (1 - tau) = 0`, and `4 tau (1 - tau) > 0` on `0 < tau < 1`. The eigenvalue
computations are recorded separately because the card states them.

Hypotheses are `0 < tau` and `tau < 1` only — the paired order's range, which is the object the
theorem quantifies over. No hypothesis is a theorem proved elsewhere in the corpus.

No `sorry`, `axiom`, `opaque`, `unsafe`, RH premise, or numerical computation occurs. Every cited
declaration audits to `[propext, Classical.choice, Quot.sound]`.

## Open boundary

The card's `(2±)` — that the fixed-window logarithmic jump of a log-conormal profile has the stated
`L^(1-tau)` expansion with the indicial matrix as its coefficient — is the asymptotic input from
the predecessor card, not reproved here. What is formalized is the exclusion that follows from it:
given `(2±)`, the matrix `(3)` is invertible on `0 < tau < 1` and its kernel at `tau = 1` is the
antisymmetric line.
