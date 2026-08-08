# Source-normal valuation-coframe transgression

- **ID:** `source-normal-valuation-coframe-transgression`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / PRODUCER TARGET
- **Status:** `[SOURCE DIFFERENTIAL CONSTRUCTED] [A_INFINITY DERIVED MODEL CONSTRUCTED]`
  `[LITERAL COMPARISON/FLATNESS OPEN] [NOT RH]`
  `[ANTI-CIRCULARITY GATES ACTIVE] [NO LEAN WRITTEN]`
- **Parent theorem:**
  `../../2-fully-proven/constraint-relativity/prime-valuation-cyclic-coframe-and-diagonal-dagger-defect-law.md`

## Problem

Current arithmetic source has complete valuation cyclic coframe

\[
 \phi_\ell([u_p])=-\delta_{\ell p},
\]

and physical dagger defect is diagonal off line. Frontier correction: strict all-prime
Euler--Gamma/Mobius source differential and exact-kernel Möbius--Fourier detector are now
paper-constructed. Missing object is no longer generic new `d_src`; it is coefficient-faithful
rational-Witt/Milnor comparison plus independent flatness of explicit source--Poisson lift
obstruction.

## Central conjecture VCT (revised)

Construct from literal rational-adelic/Gamma/co-Poisson source, before divisor specialization:

1. actual degree-two rational-Witt/Milnor realization `G_Gamma` retaining prime coframe and Xi jet;
2. comparison from pre-divisor prime-radial Koszul/Smith object to that realization;
3. source-normal semi-infinite determinant/polarization compatible with prime cutoffs;
4. literal boundary identity annihilating canonical Route-L obstruction

\[
 \boxed{
 \Omega_{\mu,\Gamma}(w_{23})
 =\mathfrak S_\mu\mathcal G_\Gamma D(w_{23})=0.}
 \tag{VCT}
\]

Existing exact obstruction theorem identifies `(VCT)` with literal Meyer--Poisson chain lift.
Coefficient-faithful Xi evaluation is `c_rho(g_2(rho)-g_3(rho))`, `c_rho!=0`; hence `(VCT)` is
RH-bearing and may not be assumed. Comparison and zero identity must both come from source.

## Why this is first viable law event

- Old cyclic differential leaves every `phi_ell` closed and is radially equivariant.
- Cross-prime cancellation is impossible coordinatewise.
- Holomorphic one-leg compensation is impossible.
- Mixed opposite charge has exact separation rank two.
- Rank-minimal fitted compensation is contractible.
- Trace-one prime tensor leaves individual leg ratio as `C^times` torsor.
- Fixed `r` infinity ports have transgression rank at least `N-r`; one port produces raw
  `A_(N-1)` conormal, not global rank-one anomaly.
- Prime-radial excess intersection now constructs one horizon port in `H_0`, full `A_(N-1)` in
  `H_1`, higher exterior coherences, and Smith jet staircase without false common inverse.
- Underived prime ideal is `(a)` after one prime; more primes add derived excess only.

Therefore remaining comparison must be genuinely mixed/two-legged, noncontractible,
source-generated, coefficient-faithful, and singular/semi-infinite enough to preserve growing
derived excess and Smith jets. One port no longer needs postulated rank collapse: it is `H_0` of
same derived object whose `H_1` is root conormal.

## Conjecture loops

### VCT-1: archimedean Kummer closure

Try extend finite valuation family by infinity valuation and use product formula. **Failed:**
principal-idèle relation is invariant under every radial character `|.|^c`; it cancels all `c`,
not only zero.

### VCT-2: sum valuation cocycles

Try scalar Kummer `sum log(ell) phi_ell`. **Failed:** it is one covector, loses prime coordinates,
and remains radial-gauge invariant.

### VCT-3: complete prime span

Try Hilbert/nuclear completion. **Failed under faithful extension:** each extended `phi_ell`
continues to separate prime coordinates; diagonal off-line defect stays injective.

### VCT-4: force a cross-grade line

Algebraically, line spanning two distinct total grades has trivial radial stabilizer. **Failed as
selector:** family `L_lambda=C(x_g+lambda x_h)` is radial torsor

\[
 \Gamma_cL_\lambda=L_{\lambda(h/g)^c}.
\]

Action is transitive on `lambda>0`; each line has trivial stabilizer. Picking `lambda=1` without
source-derived absolute calibration is gauge fixing, not gauge breaking.

### VCT-5: source-star mismatch at infinity

Candidate survivor: ordinary source dagger reverses Kummer orientation and is blind. Seek secondary
operation comparing finite-prime valuation coframe with archimedean analytic adjoint without
reversing prime class. **Advanced:** Euler--Gamma/Mobius differential and exact detector now exist;
actual rational-Witt/Milnor chain comparison and flatness remain open.

### VCT-6: singularly collapse root conormal to one port

**Replaced.** Prime-radial Koszul object has one port in `H_0` and root conormal in `H_1`; no
collapse needed. Infinite difficulty is source-normal determinant phase and comparison of derived
degrees with Route-L boundary.

## Fatal anti-theatre tests

Any candidate fails if:

1. defined after choosing `rho`;
2. inserts `Re rho=1/2`, `delta=1`, null-homology, or equivalent normality;
3. equation holds only after logarithmic contraction, not prime-by-prime;
4. erases first nonzero Xi jet or trace-one prime atom;
5. cone differential is defined to be desired multiplier;
6. operation is homogeneous under total radial grade;
7. new compensator splits as contractible fitted pair;
8. source relation is not canonical under rational-adelic symmetries;
9. generalized-prime countermodels satisfy every stated premise off line.

## First exact subproblem

For primes `{2,3}`, compare canonical generator

\[
 H_1(K_{2,3})
 =\{(c_2,c_3):c_2\log2+c_3\log3=0\}
\]

with ordered Green/Bockstein boundary `w_23`, and prove Smith classes `R/(a^j)` map to actual
leading Xi jets before completion. Then prove `(VCT)` by independent source relation. At three
primes comparison must retain two-dimensional `H_1` and length-three Smith defect before final
Stokes scalarization.

## Falsifier

Prove every source-natural extension of current rational-adelic cyclic complex commuting with
finite adèles and actual Xi coordinate action remains `Gamma_c`-equivariant. That would rule out
VCT inside present source category and force pivot to a larger source law (likely nonprincipal
prime--infinity/holographic completion).

## Lean-return note

No Lean until dependency-closed paper construction exists. Later inspect files listed in parent
Stage-2 card; do not write or build now.

## Log

- 2026-08-08 — opened after valuation-coframe theorem and radial-gauge no-go.
- 2026-08-08 — revised after source differential/detector and prime-radial excess intersection
  were constructed; frontier is literal comparison plus Route-L flatness.
