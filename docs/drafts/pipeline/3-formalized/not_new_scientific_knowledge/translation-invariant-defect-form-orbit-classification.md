# Translation-invariant defect forms are hyperbolic on every off-real orbit

- **ID:** `translation-invariant-defect-form-orbit-classification`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper); Route-A form classification
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** the semisimple theta-convolution defect and elementary unitary character theory
- **Statement:** On a semisimple complex divisor module with real translations acting by
  `T_a e_rho=exp(-i a rho)e_rho`, an invariant Hermitian form can pair `e_rho` only with
  `e_(conj(rho))`.  Every nonreal conjugate pair is therefore a hyperbolic plane in any
  nondegenerate invariant form.  A positive invariant form can be faithful only on real support.

## Setup

Let `Z subset C` be a discrete multiset stable under complex conjugation.  Ignore nilpotent
multiplicity jets and form its algebraic semisimplification

```text
D_Z=direct_sum_(rho in Z_distinct) C e_rho.
```

Real translation acts by

```text
T_a e_rho=exp(-i a rho)e_rho,    a in R.               (1)
```

Let `H` be a Hermitian form satisfying

```text
H(T_a v,T_a w)=H(v,w)                                  (2)
```

for every real `a`.

## Pairing selection rule

For two basis vectors, equations (1)--(2) give

```text
H(e_rho,e_sigma)
  =exp(-i a(rho-conj(sigma))) H(e_rho,e_sigma)          (3)
```

for every real `a`.  If the matrix coefficient is nonzero, the exponential in (3) must be one for
all `a`, so

```text
rho=conj(sigma).                                       (4)
```

Thus a real point can pair with itself, while a nonreal point can pair only with its conjugate.

## Hyperbolic off-real blocks

On the span of `e_rho,e_(conj(rho))` with `Im(rho)!=0`, the matrix of `H` is necessarily

```text
[ 0       c ]
[ conj(c) 0 ].                                         (5)
```

If `H` is nondegenerate on this pair, then `c!=0`.  The eigenvalues of (5) are `+|c|` and `-|c|`.
Hence every nonreal conjugate pair contributes one positive and one negative direction.

For Xi, evenness adds the second pair `-rho,-conj(rho)`.  A free Xi quartet therefore contributes
two hyperbolic planes when both height signs are retained, or one on an upper-height fundamental
half.

## Positivity consequence

A positive definite invariant Hermitian form has zero off-real fibers: equation (5) cannot be
positive unless `c=0`, which makes the form degenerate there.  Therefore

```text
faithful + invariant + positive
  => Z subset R.                                       (6)
```

Conversely, when `Z subset R`, assigning any positive weight to every `e_rho` produces a positive
invariant form on the algebraic direct sum.  Thus existence of some faithful positive invariant
form on the semisimple Xi defect is equivalent to all Xi zeros being real, namely RH.

The theorem classifies, rather than constructs, a source form.  A canonical form may still have
negative diagonal weights at real zeros; positivity there is a separate source requirement.

## Multiplicity warning

The theorem deliberately uses the semisimplification.  On a multiplicity-`m` local jet, translation
has a nontrivial unipotent part when `m>1`.  Full unitary Hilbertization would force `m=1`, as proved
in `theta-convolution-hilbert-analytic-defect-trilemma.md`.  An RH-only route must keep nilpotent
multiplicity data outside the positive semisimple Hilbert form.

## Gates

- [x] invariant coefficient selection rule proved
- [x] off-real block and inertia computed
- [x] faithful positive support implication proved
- [x] Xi quartet and multiplicity consequences delimited
- [x] 2 -> 3 formalized: `RHTower/TranslationInvariantDefectForm.lean`

## 2026-08-16 Lean closure

`RHTower/TranslationInvariantDefectForm.lean` proves the card unconditionally.

`divisorTranslationChar rho a i = exp(-i a rho_i)` is the translation character (1), and invariance
(2) is written entrywise on the Gram matrix `H`.

- `eq_conj_of_invariant_ne_zero` is the coefficient selection rule: `H i j != 0` forces
  `rho i = conj (rho j)`.  The proof extracts the character identity
  `exp(i a (conj rho_j - rho_i)) = 1` for every real `a` and kills the exponent by differentiating
  at `a = 0` (`eq_zero_of_exp_eq_one`), so no discreteness or lattice argument is needed.
- `diag_eq_zero_of_not_conj_self`: at a nonreal frequency the diagonal entry vanishes, so every
  off-real orbit is isotropic.
- `hyperbolicValue_pos_neg`: on an isotropic pair with off-diagonal entry `c != 0` the restricted
  form `2 Re(x conj(y) c)` takes both a strictly positive and a strictly negative value, i.e. the
  conjugate pair is a hyperbolic plane of inertia `(1,1)`.
- `rho_eq_conj_of_posDef`: a form that is nonzero on the diagonal at every frequency has real
  support only — a positive invariant form can be faithful only there.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
