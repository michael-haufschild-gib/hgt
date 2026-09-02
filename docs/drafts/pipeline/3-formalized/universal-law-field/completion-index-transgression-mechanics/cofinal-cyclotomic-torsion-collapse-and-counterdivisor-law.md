# Cofinal cyclotomic torsion collapse and counterdivisor law

- **ID:** ULF-CIT-2
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / SOURCE-MODEL NO-GO WITH POSITIVE SURVIVOR
- **Lean:** `GaloisForLFunctions.RHTower.CofinalCyclotomicTorsionCollapse`; verified
- **Statement:** A nested analytic completion that conserves one residue-cell cyclotomic torsion
  factor at every unbounded integer stage has only the zero entire compact-open limit. Any nonzero
  completion must carry an interaction counterdivisor whose local negative degree grows linearly
  against the retained local torsion.

## 1. Big-picture interpretation

Exact ordinary-integer occurrence partitions one successor orbit into `n` residue cells. The
relative determinant of the resulting cyclic cell transfer is

`tau_n(z) = (1-z^n)/(1-z) = 1+z+...+z^(n-1)`.

Thus literal residue occurrence supplies finite torsion on the unit circle. The tempting completion
law is to preserve these local torsions and multiply them over increasingly many prime or
prime-power stages. That law is impossible: one distinguished root from each stage approaches the
neutral point `z=1`, and nested conservation makes every such root persist. A nonzero entire limit
cannot have this accumulating divisor.

The positive survivor is stronger than “the product diverges.” It is an index-transgression law.
Any nonzero global completion must subtract essentially all local cyclotomic divisor degree near
the neutral point. Hence the global determinant is not the product or direct sum of prime-local
completion indices. It is a secondary interaction torsion produced by a cofinal counterchannel.

## 2. Corpus audit before theorem

Search used `scripts/formal_tools.py research` on Squier/polygraphic completion, Novikov and BNS
support, affine-semigroup boundary quotients, residue partitions, geometric-polynomial roots,
mapping-cone torsion, determinant limits, Roos classes, and cyclotomic towers.

Already proved in the corpus:

1. `finiteGeometricPolynomial_root_norm_eq_one` puts every root of `tau_n` on the unit circle.
2. `ConstitutiveCriticalCompletionMechanics` gives terminating but cofinally nonconfluent source
   execution with stationary semantic quotient.
3. `ArithmeticFormationCompletionBoundaryFusion` identifies the completion-born arithmetic class
   with Roos `lim^1`; its universal absence is RH, so derived completion is a reader.
4. `DeningerPrimePacketCyclotomicTowerAction` constructs faithful compatible arithmetic actions on
   the actual prime-power root towers.
5. `HedenmalmThetaSourceDeterminantIdentity` already gives the exact global theta determinant
   `det_2(I+zB)=XiC(z)/XiC(0)`.
6. `HurwitzClosedZeroLocus` and `BoundedDomainDivisorTransfer` contain general compact-open divisor
   transfer, but corpus search found no theorem applying accumulating residue-cell torsion to rule
   out a nested nonzero entire arithmetic completion.

External parent theory does not supply arithmetic selection. Novikov--Sikorav homology and BNS
invariants detect character chambers after a character has been chosen. Semigroup Toeplitz theory
provides several boundary quotients for `N semidirect N^times`, not a unique arithmetic one:

- Friedl, *Novikov homology and noncommutative Alexander polynomials*,
  https://arxiv.org/abs/1606.03587
- Kielak, *The Bieri--Neumann--Strebel invariants via Newton polytopes*,
  https://arxiv.org/abs/1802.07049
- Brownlowe--an Huef--Laca--Raeburn, *Boundary quotients of the Toeplitz algebra of the affine
  semigroup over the natural numbers*, https://arxiv.org/abs/1009.3678
- Laca--Sehnem, *Toeplitz algebras of semigroups*, https://arxiv.org/abs/2101.06822

No novelty priority is claimed for the identity theorem or argument principle. New content is the
exact source-model consequence and counterdivisor requirement for this corpus.

## 3. Residue-cell relative torsion

Let `C_n` be cyclic permutation of the `n` residue cells. Its characteristic determinant is

`det(I-z C_n)=1-z^n`.

Removing the common successor-vacuum factor `1-z` gives

`tau_n(z)=det(I-z C_n)/(1-z)=sum_(r=0)^(n-1) z^r`.

For `n>1`, put `zeta_n=exp(2 pi i/n)`. Then `tau_n(zeta_n)=0`. If `n_j` is strictly increasing,
the points `zeta_(n_j)` are distinct and converge to `1`.

The determinant formula follows either by diagonalizing `C_n` over the `n`th roots of unity or by
the characteristic polynomial of a cyclic permutation. The root statement is the geometric-sum
identity `(1-z) tau_n(z)=1-z^n`.

## 4. Conservative torsion collapse

### Theorem 4.1 [PROVED HERE]

Let `2 <= n_1 < n_2 < ...`. Let `F_m` be entire functions such that

`F_m(zeta_(n_j))=0` for every `j<=m`.

If `F_m` converges locally uniformly on `C` to an entire function `F`, then `F` is identically
zero.

#### Proof

Fix `j`. Every `F_m` with `m>=j` vanishes at the fixed point `zeta_(n_j)`. Local uniform
convergence implies pointwise convergence there, hence `F(zeta_(n_j))=0`. The zeros are distinct
and converge to `1`, an interior point of `C`. The identity theorem gives `F=0`. QED.

### Corollary 4.2 [PROVED HERE]

Put `P_m=product_(j=1)^m tau_(n_j)`. For arbitrary entire functions `H_m`, every locally uniform
entire limit of `P_m H_m` is identically zero.

#### Proof

Each factor `tau_(n_j)` divides every later `P_m H_m`, so Theorem 4.1 applies. QED.

The conclusion is unchanged by scalar normalization, exponential normalization, or multiplication
by any zero-free entire gauge. Such operations cannot remove a persistent divisor.

## 5. Counterdivisor conservation

The preceding collapse identifies the only escape: later stages must cancel or move earlier local
torsion. The required cancellation has a quantitative local index.

### Theorem 5.1 [PROVED HERE]

Let `D` be a closed disc centred at `1`, with positive radius. Let `F_m` be holomorphic on a
neighbourhood of `D` and converge uniformly there to a nonzero holomorphic `F`. Assume `F` has no
zero on `boundary D`. Let

`F_m = P_m R_m`,

where `P_m=product_(j=1)^m tau_(n_j)` and `R_m` is meromorphic near `D`; assume no factor has a
zero or pole on `boundary D`. Write `deg_D div(g)` for zeros minus poles in the interior of `D`,
with multiplicity. Then, for all sufficiently large `m`,

`deg_D div(R_m) <= N_D(F) - m + J_D`,

where `N_D(F)` is the number of zeros of `F` in `D` and `J_D` is a fixed integer independent of
`m`. In particular `deg_D div(R_m) -> -infinity` at least linearly.

#### Proof

Since `zeta_(n_j)->1`, choose `J_D` so `zeta_(n_j)` lies in the interior of `D` for every
`j>J_D`. These points are distinct zeros of `P_m`, so

`deg_D div(P_m) >= m-J_D`.

Uniform convergence and boundary nonvanishing let Rouche's theorem, equivalently the argument
principle, identify the zero count of `F_m` in `D` with `N_D(F)` for every sufficiently large
`m`. Divisor additivity gives

`N_D(F)=deg_D div(F_m)=deg_D div(P_m)+deg_D div(R_m)`.

Rearranging proves the inequality. QED.

### Interpretation

Local residue torsion contributes positive divisor degree. A nonzero global entire completion has
bounded divisor degree on every fixed compact window. Therefore an interaction channel must carry
asymptotically equal negative divisor degree. This is an exact conservation law, not a positivity
or coherence statement.

## 6. Hostile audit

### Survives

- The theorem is pre-divisor and uses only exact residue-cell occurrence plus analytic completion.
- It narrows the literal-source model class: primewise direct products, direct sums whose
  determinants multiply, and every torsion-conservative nested extension are excluded as nonzero
  entire completions.
- The counterdivisor estimate is invariant under zero-free gauges and retains multiplicity.
- It explains why numerical Fredholm additivity fails in the useful direction: local effective
  torsion cannot remain additive at the global analytic stage.

### Does not prove

- It does not identify the successor spectral variable with the centred Xi parameter.
- It does not construct the interaction counterdivisor from prime--Gamma coefficients.
- It does not show the surviving global torsion is supported on the critical line.
- Couplings that move all earlier cyclotomic roots evade Corollary 4.2; this is not a loophole but
  the exact nonconservative interaction that must now be constructed and controlled.

### Countermodels checked

- Zero-free entire normalizers fail because divisors persist.
- Meromorphic normalizers succeed only by paying the linearly growing negative divisor required by
  Theorem 5.1.
- Arbitrary stagewise couplings can move roots, but then local torsion is not conserved and their
  motion requires a source-derived law; fitting it to Xi is disallowed.
- Novikov/BNS support, Squier completion, Roos classes, and ax+b boundary quotients classify supplied
  completions but do not generate this cancellation.

## 7. Fourth-organ prediction and RH boundary

The Deninger/Witt cyclotomic tower is the fourth-organ test. Its faithful compatible root-tower
action cannot be promoted to an Xi determinant by multiplying stage characteristic torsions while
retaining every earlier cyclotomic divisor. Any successful promotion must exhibit a canonical
relative determinant or superdeterminant whose interaction denominator cancels cofinally all but
locally finite cyclotomic divisor degree.

For RH closure one would still need a coefficient-faithful comparison

`secondary interaction torsion = det_2(I+zB) = XiC(z)/XiC(0)`

and a source theorem that the residual, after forced cyclotomic cancellation, has no off-real
support. The present theorem does not discharge that gate. It replaces the false additive-index
architecture by a sharply constrained nonadditive one.

## 8. Formalization status

Paper proof is dependency-closed. No Lean file was written or built because current research phase
explicitly restricts work to Lean-corpus audit. A later formalization should reuse
`finiteGeometricPolynomial_root_norm_eq_one`, compact-open point evaluation, the identity theorem,
and the existing bounded-domain divisor-transfer library.

## Log

- 2026-09-01 -- proved after derived-rewriting/Novikov completion was killed as another reader.
