# Finite Möbius--Pluecker transfers lift cofinally to the reciprocal normal-cone section

- **ID:** `mobius-pluecker-normal-cone-diagonal-lift`
- **Stage:** 3-formalized
- **Type:** `[THEOREM] [HT TWOSCALE COMPLETION] [PLUECKER-TO-RECIPROCAL-HORIZON LIFT]`
- **Scientific status:** `[PROVED ON PAPER] [SOURCE-PURE] [FORMALIZED UNCONDITIONALLY IN LEAN 4] [NOT RH]`
- **Parents:**
  - `../3-formalized/not_new_scientific_knowledge/mobius-finite-schur-coisometry-core.md`;
  - `../3-formalized/mobius-prime-loschmidt-purity-survival.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/mobius-squarefree-reciprocal-projective-transfer.md`;
  - `../3-formalized/mobius-mellin-gamma-normal-cone.md`.

## 1. Finite Pluecker transfer

Let `S` be a finite prime set, `sigma>1`, and `Re s>1`.  The normalized signed squarefree
Loschmidt amplitude is

```text
tau_(S,sigma)(s)
 =product_(p in S) (1-p^(-s))/(1+p^(-sigma)).             (1)
```

The safe squarefree correction is

```text
c_(S,sigma)(s)
 =product_(p in S) (1-p^(-2sigma))/(1-p^(-2s)).          (2)
```

Cancelling `1-p^(-2s)=(1-p^(-s))(1+p^(-s))` gives the finite reciprocal transfer

```text
M_(S,sigma)(s)
 :=c_(S,sigma)(s) tau_(S,sigma)(s)
 =product_(p in S) (1-p^(-sigma))/(1+p^(-s)).            (3)
```

Every factor in `(1)` is the matrix coefficient of the finite squarefree Pluecker state against
its parity-reflected logarithmic translate.  Thus `(3)` is a finite source object; no zeta zero or
continued divisor is used.

## 2. Fixed-aperture no-go

For fixed finite `S`,

```text
M_(S,1+epsilon)(s)
 ->product_(p in S)(1-p^(-1))/(1+p^(-s)) !=0.            (4)
```

Therefore

```text
M_(S,1+epsilon)(s)/epsilon
```

does not converge to a finite reciprocal-horizon section as `epsilon->0+`.  The Euler normal cone
cannot appear at any fixed prime aperture.  Prime depth and critical scale must tend to their
boundaries jointly.

**Positive HT theorem.**  The reciprocal exceptional divisor is a genuinely two-filtered
completion class: every finite source chart misses it, but a bornologically cofinal diagonal may
retain it.

## 3. Cofinal diagonal-lift theorem

Let `epsilon_n>0` tend to zero and put `sigma_n=1+epsilon_n`.  There exists a nested sequence of
finite prime sets

```text
S_1 subset S_2 subset ...                                (5)
```

whose union is all primes and such that

```text
M_(S_n,sigma_n)(s)/epsilon_n
 ->1/Z_sq(s)=zeta(2s)/zeta(s)                            (6)
```

locally uniformly on `Re s>1`.

### Proof

For every fixed `sigma>1`, absolute Euler-product convergence gives

```text
M_(S,sigma)(s)
 ->M_sigma(s)
 =1/[zeta(sigma)Z_sq(s)]                                 (7)
```

locally uniformly on `Re s>1` as `S` runs cofinally through the finite prime sets.  Let
`K_1 subset K_2 subset ...` be a compact exhaustion of that half-plane.  At stage `n`, choose a
finite prime set `S_n` containing `S_(n-1)` and the first `n` primes such that

```text
sup_(s in K_n)
 |M_(S_n,sigma_n)(s)/epsilon_n
   -M_(sigma_n)(s)/epsilon_n| <1/n.                      (8)
```

This is possible by `(7)`; the factor `epsilon_n^(-1)` only changes the requested finite-stage
tolerance.  The residue unit

```text
G(sigma)=(sigma-1)zeta(sigma),       G(1)=1              (9)
```

gives

```text
M_(sigma_n)(s)/epsilon_n
 =1/[G(sigma_n)Z_sq(s)]
 ->1/Z_sq(s)                                             (10)
```

locally uniformly.  Equations `(8)`--`(10)` prove `(6)`.  Adding the first `n` primes makes the
union in `(5)` cofinal without changing the approximation argument. `QED`

## 4. Gamma-completed exceptional lift

On `Re s>1`, the archimedean factor `C(s)` is nonzero.  Multiplying `(6)` by `C(s)^(-1)` therefore
gives

```text
C(s)^(-1)M_(S_n,sigma_n)(s)/epsilon_n
 ->1/X_sq(s).                                            (11)
```

The projectivized square of the right side is the proved reciprocal HT horizon transition

```text
-X_sq(s)^(-2),                                           (12)
```

whose logarithmic connection is `Q_sq` and whose anti-causal Hardy component is `ell_E`.

Thus the exceptional section used by the Gauss--Ward conjecture is not adjoined after analytic
continuation.  It is a locally uniform diagonal limit of the actual finite Pluecker/Loschmidt
source transfers on their Euler half-plane.

## 5. Lean formalization

The exact dependency-closed theorem is formalized in
`formal/GaloisForLFunctions/RHTower/MobiusPlueckerNormalConeDiagonalLift.lean` and exported through
`GaloisForLFunctions.RHTower`.

The module proves the finite source/product identity, the fixed-aperture nonzero limit and resulting
failure of finite normalized convergence, locally uniform Euler-product convergence, compact
exhaustion diagonal selection with nested cofinal finite prime sets, Gamma completion, and the
projectivized negative reciprocal square.  Its capstone is
`exists_mobiusPlueckerCompletedDiagonal`; supporting endpoint theorems include
`finiteMobiusPlueckerAmplitude_eq_prod`,
`not_tendsto_finiteMobiusPlueckerTransfer_div_epsilon`,
`exists_mobiusPlueckerDiagonal`, `mobiusPlueckerGammaCompleted`, and
`mobiusPlueckerProjectivizedSquare`.

Audit evidence:

- `lake env lean GaloisForLFunctions/RHTower/MobiusPlueckerNormalConeDiagonalLift.lean` passes;
- `lake build GaloisForLFunctions.RHTower.MobiusPlueckerNormalConeDiagonalLift` passes;
- `scripts/formal_tools.py lint` passes after umbrella wiring;
- `#print axioms` for the finite source identity, fixed-aperture no-go, and completed-diagonal
  capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.

## 6. Exact remaining boundary

The theorem constructs the algebraic/analytic Rees section but does not transport the positive
Pluecker metric through `Re s=1`.  Local uniform convergence on `Re s>1` does not control the
unweighted anti-Hardy trace on `Re s=1/2`; assuming that control would be the Ward estimate.

The next theorem must equip the diagonal `(5)` with the HT source graph norm and prove that its
closed singular Hermitian form has exceptional second fundamental form `Q_sq`.  If the form stays
positive, Gauss--Codazzi gives `||ell_E||_2^2<=4` and RH.

If it fails, the nonclosability or negative part is a nontrivial **normal-cone polarization
defect** of the general HT source.  This is stronger than merely saying that analytic continuation
is difficult: it identifies the exact positive structure lost between a cofinal source lift and
its opposite-polarization boundary trace.

## Gates

- [x] finite reciprocal transfer derived from the actual Möbius/Pluecker source
- [x] fixed-aperture normal-cone limit ruled out
- [x] nested cofinal diagonal constructed for every critical sequence
- [x] local-uniform reciprocal-squarefree limit proved
- [x] Gamma-completed exceptional lift proved on `Re s>1`
- [x] formalize the locally uniform diagonal selection theorem
- [ ] construct the closed singular Hermitian graph form
- [ ] control the exceptional Hardy second fundamental form
- [ ] four-unit estimate
- [ ] RH
