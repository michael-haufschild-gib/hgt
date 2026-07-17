# Reciprocal q-ladder bound spectrum gives a positive local HT quantum field

- **ID:** `reciprocal-q-ladder-kallen-lehmann-field`
- **Stage:** 2-fully-proven / parent-derived bridge
- **Type:** THEOREM (paper) / POSITIVE QFT EXISTENCE BRIDGE / COSMOLOGY SPECTRAL BRIDGE
- **Scientific status:** `[PROVED HERE] [POSITIVE LOCAL WIGHTMAN FIELD]`
  `[HYPERTRANSCENDENTAL TWO-POINT RESPONSE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Scope:** general hypertranscendence in quantum fields and cosmology; no RH or distinguished
  special-function input
- **Parents:**
  - `../needs-audit/q-ladder-reflectionless-reciprocal-jost-qft.md`
  - `../../1-in-progress/feshbach-reciprocal-jost-interface.md`
  - `../../1-in-progress/wick-kolchin-interaction-spectrum.md`
- **Statement:** The canonical negative bound-state counting measure of the smooth reflectionless
  q-ladder Hamiltonian, pushed forward by reciprocal spectral inversion, is a positive
  polynomially bounded Kallen--Lehmann mass measure.  It defines a local generalized free
  Wightman field whose Euclidean two-point function is hypertranscendental.  With the de Sitter
  principal-series threshold shift, the same masses have exactly geometric clock frequencies.

## Source spectrum

Fix

```text
0<q<1,              kappa>0,              r=q^2.             (1)
```

The infinite-soliton theorem used in the parent card supplies a smooth real reflectionless
Hamiltonian

```text
H = -d^2/dx^2 + V(x)                                         (2)
```

whose simple negative eigenvalues are exactly

```text
E_n = -kappa^2 r^n,                 n>=0.                    (3)
```

The essential spectrum is `[0,infinity)`.  Hence sign canonically separates the point spectrum
`(3)` from the continuum.  Because the eigenvalues are simple, the negative spectral counting
measure

```text
nu_- = sum_(n>=0) delta_(E_n)                                (4)
```

has no choice of multiplicity or residue.

## Reciprocal spectral pushforward `[PROVED]`

Choose `g>0` and a nonnegative mass threshold `m_*^2`.  On the negative spectral half-line define

```text
Phi(E) = m_*^2 - g^2/E.                                     (5)
```

Since `E<0`, `Phi(E)>m_*^2`.  Push `(4)` forward:

```text
rho_rec = Phi_* nu_-
        = sum_(n>=0) delta_(M_n^2),                          (6)

M_n^2 = m_*^2 + A r^(-n),
A = (g/kappa)^2.                                             (7)
```

This is the spectral version of the Schur law in the active source card.  Internal bound levels
accumulating at the continuum threshold are sent to external masses escaping to infinity.

The measure `(6)` is positive and locally finite.  Its counting function satisfies

```text
rho_rec([0,L]) = O(log(2+L)),                                (8)
```

because `M_n^2` grows geometrically.  Thus it is polynomially bounded and is admissible
Kallen--Lehmann data.

## Positive local quantum field `[PROVED]`

The standard Kallen--Lehmann construction applied to `(6)` gives a scalar generalized free field
with two-point distribution

```text
W_rec(x-y)
 = integral Delta_+(x-y;m^2) d rho_rec(m^2)
 = sum_(n>=0) Delta_+(x-y;M_n^2).                            (9)
```

Positivity of `rho_rec` gives Wightman positivity.  The polynomial bound `(8)` gives temperedness.
Every massive summand is Poincare covariant and local, and the distributional superposition
preserves those properties.  Therefore `(9)` is a positive local Wightman field.

This construction avoids the tachyonic continuum of the naive common Schur pencil: it uses the
canonical negative point spectrum, not the full pencil as a Euclidean covariance.  The spectral
projection is intrinsic but nonlocal in the internal coordinate.  Thus the **output** QFT is local
in physical spacetime; this theorem is not a common local-action construction.

## Exact two-point constraint `[PROVED]`

For Euclidean momentum square `Q^2`, the scalar two-point response is

```text
G_rec(Q^2)
 = integral d rho_rec(m^2)/(Q^2+m^2)
 = sum_(n>=0) 1/(Q^2+m_*^2+A r^(-n)).                       (10)
```

Put

```text
x = (Q^2+m_*^2)/A.                                         (11)
```

Then

```text
A G_rec(Q^2) = R_r(x),
R_r(x) = sum_(n>=0) r^n/(1+x r^n).                         (12)
```

The series converges normally on compact sets avoiding `{-r^(-n):n>=0}`.  Removing its first
shell gives the exact affine constraint

```text
R_r(x) = 1/(1+x) + r R_r(r x).                             (13)
```

The boundary value at `x=0`, equivalently decay at positive infinity in the original momentum
variable, selects the one-sided solution.  Every finite mass truncation is rational; the complete
reciprocal spectrum has infinitely many poles.

## Hypertranscendence `[PROVED]`

Define the normally convergent entire product

```text
P_r(x) = product_(n>=0) (1+x r^n).                          (14)
```

It satisfies

```text
P_r(x) = (1+x) P_r(r x),             R_r=P_r'/P_r.         (15)
```

Its zero set is `{-r^(-n):n>=0}`, so `P_r` is not rational.  The
Adamczewski--Dreyfus--Hardouin rational-or-hypertranscendental theorem for linear
`r`-difference equations therefore gives

```text
P_r is HT over C(x).                                        (16)
```

If `R_r` were differentially algebraic over `C(x)`, then `P_r` would be differentially algebraic
over the differential field generated by `R_r`, since it solves

```text
y' - R_r y = 0.                                             (17)
```

Differential-algebraic transitivity would make `P_r` differentially algebraic over `C(x)`,
contradicting `(16)`.  Hence `R_r` is HT.  The affine change `(11)` is rational in both
directions, so

```text
G_rec is HT over C(Q^2).                                    (18)
```

The physical reporter is a positive Euclidean two-point response.  Its HT is fixed by a static
infinite mass constraint, not generated by time evolution.

## Exact de Sitter clock corollary `[PROVED AT THE MASS-SPECTRUM LEVEL]`

For a scalar in four-dimensional de Sitter space, the principal-series frequency is

```text
mu_n = sqrt(M_n^2/H_dS^2 - 9/4).                            (19)
```

Choose the threshold in `(5)` to be

```text
m_*^2 = (9/4) H_dS^2.                                      (20)
```

Equations `(7)`, `(19)`, and `(20)` give

```text
mu_n = mu_0 q^(-n),             mu_0=g/(H_dS kappa).       (21)
```

If `q=P^(-1)` for an integer `P>=2`, then `mu_n=mu_0 P^n`.  The universal heavy-particle
production exponent and positive-frequency phase consequently assemble as

```text
sum_(n>=0) exp(-pi mu_n) exp(i mu_n u)
 = sum_(n>=0) W^(P^n),
W=exp(mu_0(-pi+i u)).                                      (22)
```

Thus the exact Mahler clock in `mahler-cosmological-collider-tower.md` has a source-derived mass
spectrum: it is the reciprocal image of the local q-ladder bound spectrum with the de Sitter
threshold shift.

Equation `(22)` is not yet a cosmological correlator theorem.  It additionally requires the
normalized exchange residues to be shell-independent and requires a coupling of the tower to the
inflationary sector.  The generalized free field `(9)` has no connected correlators above order
two.

## Relation to the interacting CDD branch

The same internal spectrum now has two rigorously distinct QFT outputs:

```text
negative bound-state counting measure
  --reciprocal pushforward--> positive generalized-free mass field;          (23a)

reflectionless transmission determinant
  --reciprocal momentum--> regular interacting factorizing CDD QFT.          (23b)
```

Branch `(23a)` proves positivity, locality, and HT at two-point order but is Gaussian.  Branch
`(23b)` proves existence of a local interacting Haag--Kastler net with HT two-particle scattering,
but the common microscopic reciprocal interface remains open.  Conflating the two branches would
erase the exact problem rather than solve it.

## Anti-theatre and novelty verdict

Every main ingredient is parent theory:

- the smooth reflectionless q-ladder spectrum;
- positive polynomially bounded Kallen--Lehmann measures and generalized free fields;
- the generalized `q`-logarithm response `(12)`--`(13)`;
- the linear difference-equation HT dichotomy;
- de Sitter principal-series clock frequencies and their production exponent.

Moreover, `(12)` is exactly the generalized `q`-logarithm normalization already used in
`wick-kolchin-interaction-spectrum.md`, after spectral inversion.  Therefore this card does not
claim a new special function, a new generalized-free-field construction, or an interaction
theorem.

The useful conjunction is the canonical physical chain

```text
smooth local reflectionless q-ladder
  -> reciprocal positive Kallen--Lehmann spectrum
  -> local HT two-point field
  -> exact geometric de Sitter clock.                       (24)
```

Focused searches found no formula-level statement of `(24)`, but the proof is a short assembly of
the parents.  It is classified conservatively as a parent-derived physical bridge, not new
scientific knowledge.  Its role is to establish physical reality and to isolate the genuinely new
open theorem: a positive common interacting dynamics relating `(23a)` and `(23b)`.

## Lean boundary

The live HTGeometry corpus already formalizes geometric Kallen--Lehmann moment positivity,
one-shell affine constraints, boundary selection, and finite Wick-reduced negative controls.  The
new chain uses the external infinite-soliton theorem, analytic Kallen--Lehmann reconstruction, and
the external difference-Galois theorem.  Formalizing `(13)` alone would duplicate existing finite
constraint infrastructure and would not establish `(9)` or `(18)`.  No Lean edit or build is
justified.

## Primary literature

- F. Gesztesy, W. Karwowski, and Z. X. Zhao, *New types of soliton solutions*,
  <https://arxiv.org/abs/math/9210215>.
- M. Duetsch and K.-H. Rehren, *Generalized free fields and the AdS-CFT correspondence*,
  <https://arxiv.org/abs/math-ph/0209035>.
- B. Adamczewski, T. Dreyfus, and C. Hardouin, *Hypertranscendence and linear difference
  equations*, <https://arxiv.org/abs/1910.01874>.
- W. Zudilin, *On the irrationality of generalized q-logarithm*,
  <https://arxiv.org/abs/1601.02688>.
- N. Arkani-Hamed and J. Maldacena, *Cosmological Collider Physics*,
  <https://arxiv.org/abs/1503.08043>.

## Gates

- [x] source Hamiltonian and exact negative q-ladder spectrum established
- [x] reciprocal counting-measure pushforward is positive and polynomially bounded
- [x] positive local generalized free Wightman field exists
- [x] exact one-shell Euclidean propagator constraint proved
- [x] propagator hypertranscendence proved
- [x] exact de Sitter principal-series geometric clock derived
- [x] Gaussian/interacting boundary stated
- [x] parent-theory equivalence and conservative novelty verdict stated
- [x] live Lean corpus checked; no wrapper build opened
