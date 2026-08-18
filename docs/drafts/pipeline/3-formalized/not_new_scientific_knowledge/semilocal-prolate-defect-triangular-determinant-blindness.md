# Semilocal prolate defect is triangularly determinant-blind

- **ID:** semilocal-prolate-defect-triangular-determinant-blindness
- **Stage:** 3-formalized
- **Type:** THEOREM / ROUTE GATEKEEPER (paper)
- **Scientific status:** BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source input:** the cyclic-pair filtrations and formal prolate operators of
  Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*, arXiv:2310.18423v2,
  Sections 2 and 4.3

## Statement

Let `E_n^infinity` and `E_n^P` be the degree-`n` cyclic filtrations for the archimedean and finite
semilocal cyclic pairs. Let `J_P` be the identity on polynomial functions, so

`J_P(E_n^infinity)=E_n^P`.

Put

`B_P=J_P^(-1)N_PJ_P-N_infinity`

on the archimedean polynomial core. Then

`B_P(E_n^infinity) subset E_(n-1)^infinity`                 (1)

for every `n>=0`, with `E_(-1)=0`. Hence `B_P` is locally nilpotent:

`B_P^(n+1)|_(E_n^infinity)=0`.                              (2)

For every finite truncation,

`det(I+z B_P|_(E_n^infinity))=1`.                           (3)

If `B_P` has any compact extension to the completed Hilbert space, that extension is quasinilpotent.
If it has a trace-class extension, its Fredholm determinant is identically trivial:

`det_F(I+zB_P)=1` for every complex `z`.                    (4)

The pulled-back formal prolate naturality defect is `lambda^2B_P`; it has the same conclusions. Thus
the raw defect cannot yield a nontrivial ordinary or Fredholm determinant even though its
ground-state row contains the infinite alternating nonzero tower proved in
`semilocal-all-even-jacobi-prolate-residue-tower.md`.

## Proof

The number operator associated to a cyclic pair acts by `n` on the one-dimensional graded quotient

`E_n/E_(n-1)`.

Indeed its degree-`n` orthonormal polynomial is an eigenvector of eigenvalue `n`, while all lower
orthonormal polynomials lie in `E_(n-1)`. Since `J_P` identifies the polynomial filtrations, both
`J_P^(-1)N_PJ_P` and `N_infinity` induce multiplication by the same scalar `n` on
`E_n^infinity/E_(n-1)^infinity`. Their difference therefore maps `E_n` into `E_(n-1)`, proving (1).
Iteration proves (2), and (3) follows because the finite matrix is strictly triangular.

Now suppose `B_P` extends compactly. Let `Pi_n` be the orthogonal projection onto `E_n^infinity`.
Since `Pi_n` converges strongly to the identity and `B_P` is compact,

`Pi_n B_P Pi_n -> B_P`

in operator norm. Every approximant is finite-rank nilpotent by (2). Nonzero eigenvalues of compact
operators, counted with algebraic multiplicity inside an isolated contour, are stable under sufficiently
small norm perturbations. A nonzero eigenvalue of `B_P` would therefore force a nearby nonzero
eigenvalue of all sufficiently large nilpotent approximants, impossible. Hence the compact extension has
spectrum `{0}` and is quasinilpotent.

For a trace-class extension, the Fredholm determinant is the product over eigenvalues with algebraic
multiplicity. All eigenvalues are zero, giving (4). Equivalently all finite truncation determinants are
one and the trace-class determinant is their canonical limit.

Finally the source formal prolate operators share the multiplication term `-D^2`, which intertwines
`J_P`. Therefore

`J_P^(-1)(W_(lambda,P)J_P-J_PW_(lambda,infinity))=lambda^2B_P`,

and scalar multiplication preserves strict lowering, local nilpotence, quasinilpotence, and determinant
triviality.

## Route consequence

- `[CLOSED]` Determinants of finite Jacobi truncations of the raw grading/prolate naturality defect
  are identically one.
- `[CLOSED]` Declaring the raw defect trace class would not create a determinant invariant; its
  Fredholm determinant would still be one.
- `[PROVED]` Nonzero low-mode or all-mode coefficients do not contradict determinant blindness:
  strictly triangular nilpotent matrices can have many nonzero entries.
- `[OPEN CORE]` A relative resolvent can mix the filtration and need not remain triangular. It is the
  only determinant variant not killed by this theorem, but it requires source-selected closed
  realizations and Schatten estimates.

## Novelty audit

Strict filtration lowering and determinant blindness are standard triangular-operator consequences.
The application decisively removes a Route B shortcut but is derivable from the parent cyclic-pair
filtration, so it is classified as BRIDGE rather than new scientific knowledge.


## Lean formalization (stage 3)

Unconditional and axiom-clean (`propext, Classical.choice, Quot.sound` only), wired into the
`HTGeometry` umbrella and built:

- `formal/GaloisForLFunctions/HTGeometry/StrictlyLoweringFiltration.lean`
- `formal/GaloisForLFunctions/HTGeometry/TriangularKernelDeterminant.lean`
- `formal/GaloisForLFunctions/HTGeometry/QuasinilpotentLowering.lean`

### Equation (1) — strict lowering from equal graded scalars

```text
structure StrictlyLowering (E : ℕ → Submodule K V) (B : V →ₗ[K] V) : Prop where
  mono   : Monotone E
  bottom : ∀ v ∈ E 0, B v = 0
  step   : ∀ n, ∀ v ∈ E (n + 1), B v ∈ E n

strictlyLowering_sub_of_graded (hmono : Monotone E) (N₁ N₂ : V →ₗ[K] V) (c : ℕ → K)
  (hbot  : ∀ v ∈ E 0, N₁ v = c 0 • v ∧ N₂ v = c 0 • v)
  (hstep : ∀ n, ∀ v ∈ E (n+1), N₁ v - c (n+1) • v ∈ E n ∧ N₂ v - c (n+1) • v ∈ E n) :
  StrictlyLowering E (N₁ - N₂)
```

This is exactly the card's derivation: both `J_P^{-1} N_P J_P` and `N_∞` induce multiplication by
the same scalar on `E_n / E_{n-1}`, so their difference maps `E_n` into `E_{n-1}`.

### Equation (2) — local nilpotence

```text
StrictlyLowering.pow_apply_eq_zero : ∀ n, ∀ v ∈ E n, (B ^ (n + 1)) v = 0
StrictlyLowering.eigenvalue_eq_zero : v ∈ E n → v ≠ 0 → B v = lam • v → lam = 0
```

### Equation (3) — the truncation determinants

In a basis adapted to the filtration the matrix is strictly triangular
(`strictlyUpper_toMatrix`), so

```text
det_one_add_smul_of_adapted (b : Module.Basis (Fin N) K W) (B : W →ₗ[K] W)
  (hB : ∀ j, B (b j) ∈ span K (b '' {i | (i:ℕ) < (j:ℕ)})) (z : K) :
  LinearMap.det (LinearMap.id + z • B) = 1
```

together with the underlying matrix facts `det_one_add_smul_of_strictlyUpper`,
`strictlyUpper_pow`, `trace_pow_eq_zero_of_strictlyUpper`, `pow_eq_zero_of_strictlyUpper`.

`det_one_add_smul_full` records the `[PROVED]` route consequence explicitly: the matrix with
*every* entry above the diagonal equal to `1` still has `det (1 + zM) = 1`, so nonzero low-mode or
all-mode coefficients do not contradict determinant blindness.

`StrictlyLowering.smul` records that the pulled-back prolate defect `λ² B_P` inherits every
conclusion.

### Equation (4) — quasinilpotence and the Fredholm determinant

**Compact extension.**  Formalized without Riesz eigenvalue-perturbation theory.  Past the
nilpotence index the powers factor through the complementary block,

```text
pow_succ_eq_mul_shrink : (B ^ m) * P = 0 → B ^ (m+1) = (B ^ m) * ((1 - P) * B)
norm_pow_le_geometric  : ‖B ^ (n+1+j)‖ ≤ ‖B ^ (n+1)‖ * ‖(1 - P n) * B‖ ^ j
```

so every spectral point obeys `‖λ‖ ≤ ‖(1 - P n) B‖` (`norm_le_shrink_of_mem_spectrum`, via
`spectrum.pow_mem_pow`).  Compactness supplies the shrinking, because the image of the unit ball is
totally bounded:

```text
tendsto_norm_comp_of_isCompactOperator (Q : ℕ → H →L[ℂ] H) (hbdd : ∀ n, ‖Q n‖ ≤ 1)
  (hptw : ∀ x, Tendsto (fun n => Q n x) atTop (𝓝 0)) (B) (hB : IsCompactOperator B) :
  Tendsto (fun n => ‖Q n * B‖) atTop (𝓝 0)

eq_zero_of_mem_spectrum_of_isCompactOperator : ... → lam ∈ spectrum ℂ B → lam = 0
```

**Trace-class extension.**  In the adapted orthonormal basis the kernel is strictly triangular, so
every kernel power has vanishing diagonal, hence vanishing trace, hence the regularized exponent is
*termwise* zero:

```text
StrictlyUpperKernel K : Prop := ∀ i j : ℕ, j ≤ i → K (i, j) = 0
hsPow_eq_zero_of_strictlyUpper : ∀ n i j, j ≤ i + n → hsPow K n (i, j) = 0
fredholmExp_eq_zero  : fredholmExp K z = 0
fredholmDet_eq_one   : fredholmDet K z = 1
fredholmDet1_eq_one  : fredholmDet1 K z = 1
```

The last is equation `(4)`: `det_F(I + zB) = 1` **for every complex `z`**, with no convergence
restriction, because the determinant exponent series vanishes term by term.  The corpus's
Hilbert--Schmidt/Fredholm formalism (`HTGeometry/HilbertSchmidt.lean`,
`HTGeometry/FredholmDeterminant.lean`, `HTGeometry/FredholmDeterminantExamples.lean`) supplies
`hsPow`, `fredholmExp`, `fredholmDet`, `hsTraceDiag`, `fredholmDet1`.

The `[OPEN CORE]` — a relative resolvent that mixes the filtration and need not stay triangular —
is not addressed, as the card requires.

**Stage:** 3-formalized.
