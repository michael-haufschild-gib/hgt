# Archimedean Schwartz restriction to a nonzero rational lattice is \(\ell^1\)

- **ID:** `ccm-rational-archimedean-schwartz-lattice`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** arithmetic-orbit subproblem of `kreal-quaternionic-ccm-cokernel`
- **Statement:** for \(f\in\mathcal S(\mathbb R,\mathbb C)\) and \(a\in\mathbb R^\times\),
  the sequence \(n\mapsto f(an)\) on \(\mathbb Z\) is absolutely summable.

## Theorem

For every Schwartz function \(f:\mathbb R\to\mathbb C\) and nonzero real scale \(a\),
\[
  \sum_{n\in\mathbb Z}\lVert f(an)\rVert<\infty.
\]

## Proof

Let \(S=p_{2,0}(f)\). The defining Schwartz seminorm estimate gives
\[
  |x|^2\lVert f(x)\rVert\le S.
\]
For \(n\ne0\), substitute \(x=an\) and divide by the positive number
\(|a n|^2\):
\[
  \lVert f(an)\rVert
  \le \frac{S}{|a|^2}\frac1{n^2}.
\]
The majorant is summable on \(\mathbb Z\), because the integer \(p\)-series converges for
\(p=2\). The omitted \(n=0\) term is finite, so comparison proves the claim.

## Hostile audit

- Nonzero scale is necessary for this argument: at \(a=0\), a nonzero value \(f(0)\) repeats
  infinitely.
- This proves the archimedean lattice estimate only. It does not prove that finite-adele compact
  support restricts rational denominators to one lattice.
- It proves fixed-scale summability, not the strong-Schwartz estimates in the idele-class base
  parameter.
- No Poisson formula, zero spectrum, positivity, RH premise, or numerical computation is used.

## Strongest positive survivor

Once a finite Bruhat factor forces supported rational points into \(N^{-1}\mathbb Z\), boundedness
of that factor and this theorem imply the fixed-base \(\ell^1(\mathbb Q^\times)\) coefficient
estimate needed by the weighted-shift trace-class theorem.

## Gates

- [x] exact conjecture
- [x] dependency-closed paper proof
- [x] formalize in Lean 4
- [ ] prove finite-adele denominator confinement
- [ ] prove strong-Schwartz dependence in the idele-class parameter

## Lean realization

- **Module:** `GaloisForLFunctions.RHTower.CCMRationalArchimedeanSchwartzLattice`
- **Capstone:** `ccmRationalArchimedeanSchwartz_lattice_summable`
- **Verification:** direct `lake env lean` check, cached leaf-module build, and `#print axioms`
  audit passed. Capstone depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-07-25 — isolated and proved the archimedean half of rational adelic orbit summability;
  no computation or RH input used.
- 2026-07-25 — formalized the seminorm comparison with the integer \(p=2\) series in Lean.
