# Multiple-zero holographic horizons are bosonic number-state varieties

- **ID:** `multiple-zero-bosonic-number-state-horizon`
- **Stage:** 1-in-progress
- **Type:** THEOREM PROGRAM / QUANTUM SPECTRAL GEOMETRY
- **Scientific status:** `[CONJECTURE: FULL PHASE] [LOCAL CORE TO FORMALIZE] [NOVELTY UNVERIFIED]`
- **Parent:** `hypertranscendental-holographic-horizon-qft-selection-law`
- **Methods:** symbolic proof, primary-source audit, and unconditional Lean formalization; no numerical computation
- **Statement:** At a zero of multiplicity `m`, the highest-pole residues of normalized derivative
  correlators are the falling factorials `(m)_k`.  These are exactly the normally ordered
  `k`-particle moments of the bosonic number state `|m>`.  Consequently a spectral determinant with
  unbounded eigenvalue degeneracies has a boundary principal-symbol variety equal to the bosonic
  number-state moment curve.  For oscillator degeneracy polynomials, the energy-marked boundary
  ideal recovers the bulk spatial dimension.

## Local theorem target

Let `F` be analytic near `rho`, with exact zero multiplicity `m`, and write

```text
F(rho+z) = z^m U(z),  U(0) != 0.
```

For `1 <= k <= m`, define the full/covariant correlator

```text
Z_k(z) = F^(k)(rho+z) / F(rho+z).
```

The target unconditional theorem is

```text
lim_(z->0) z^k Z_k(z) = m*(m-1)*...*(m-k+1).                (1)
```

The right side is the factorial moment

```text
<m| (a^dagger)^k a^k |m>.                                  (2)
```

For finite height `q`, let `X_k` represent the principal symbol of `Z_k`.  As `m` ranges through an
unbounded set, the Zariski closure of the boundary frames is the falling-factorial curve

```text
X_1 = T,
X_(k+1) = X_k * (T-k).                                      (3)
```

The target algebraic theorem is that the complete relation ideal is

```text
I_q = (X_1-T, X_(k+1)-X_k*(T-k) : 1<=k<q),                 (4)
```

or, after eliminating `T`,

```text
J_q = (X_(k+1)-X_k*(X_1-k) : 1<=k<q).                      (5)
```

Thus the highest-pole boundary does not merely resemble bosonic Fock space: it is the affine
moment variety of its number eigenstates.

## Spectral-determinant realization

`[CONJECTURE: ACTUAL CARRIER, STANDARD ANALYTIC INPUT]` If `H` has an eigenvalue `E_n` of finite
degeneracy `m_n`, its zeta-regularized characteristic determinant has a zero of multiplicity `m_n`
at spectral shift `-E_n`.  Equations `(1)--(5)` then identify the boundary correlator frame at that
crossing with the number state `|m_n>`.

Barnes multiple-gamma determinants are the natural hypertranscendental carrier.  The Barnes `G`
function already has zero multiplicities `1,2,3,...`; higher Barnes gamma functions carry the
polynomial degeneracies of higher-dimensional oscillator lattices.  The actual Barnes carrier,
including product convergence, exact zero divisor, and spectral determinant identification, must
be constructed unconditionally in Lean before promotion.

## Dimension reconstruction target

For the isotropic oscillator in spatial dimension `d`, the level-`n` degeneracy is

```text
m_d(n) = choose(n+d-1,d-1).                                 (6)
```

Adjoin the energy coordinate `N=n` to the horizon frame.  Its relation ideal contains

```text
X_1 - choose(N+d-1,d-1),                                   (7)
```

and the remaining `X_k` are forced by `(3)`.  The minimal polynomial degree of the multiplicity
coordinate in `N` is `d-1`; hence the energy-marked boundary coordinate algebra recovers `d`.
The target is a coordinate-invariant formulation via the filtered Hilbert polynomial, not a
chosen-coordinate degree count.

## Counterattacks

1. Formula `(1)` is local Leibniz calculus and is not independently new.
2. Falling factorials are classical bosonic factorial moments; `(2)` is not independently new.
3. Zero multiplicities already encode spectral degeneracies.  A repackaging of that tautology does
   not pass the significance gate.
4. The candidate new object is the complete principal-symbol relation ideal and its functorial
   reconstruction from a hypertranscendental determinant, not the individual ingredients.
5. Dimension recovery from degeneracy growth is classical in spectral geometry.  The claim must
   show a stronger invariant or equivalence than Weyl-law recovery.
6. Barnes multiple gamma may be only an example of a universal local theorem and therefore too
   narrow for a new field.

## RH impact

For a completed-zeta spectral model, the same local law would encode the multiplicity of each zero
as a number-state boundary point.  It does not constrain the horizontal location of any zero and
therefore gives no RH implication.  Its useful RH impact is diagnostic: a Hilbert--Polya model must
couple the energy coordinate to the boundary ideal; multiplicity-only holography is location-blind.

## Unconditional Lean gate

- [ ] multiplicity-`m` normalized-derivative limit `(1)`
- [ ] complete falling-factorial relation ideal `(4)--(5)`
- [ ] pole filtration modulo the relation ideal
- [ ] actual Barnes `G` or multiple-gamma carrier
- [ ] energy-marked coordinate-invariant dimension theorem
- [ ] primary parent-theory and priority audit
- [ ] paper-level significance gate
- [ ] Fields-Medal gate

Every promoted proof must be unconditional in Lean with no project axioms, `sorry`, `admit`,
`opaque`, or `unsafe` escape.
