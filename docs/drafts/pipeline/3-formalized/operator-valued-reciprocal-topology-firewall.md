# Operator-valued reciprocal-topology firewall

- **ID:** operator-valued-reciprocal-topology-firewall
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** cross-corpus L/R/CCM/P retirement audit
- **Statement:** If Hilbert--Schmidt kernels `K_n` converge to `K_0` in Hilbert--Schmidt norm, then their canonical entire Hilbert--Carleman determinants `entireDet2 K_n` converge to `entireDet2 K_0` at every fixed spectral coordinate; hence a fixed selected zero cannot persist along the approximants when the limiting determinant is nonzero there.

## Goal

Close the operator-valued loophole left by scalar descent retirement. A source-to-operator producer may
move a divisor rather than multiply a determinant by a scalar. This theorem proves that it still cannot
do so continuously from a reciprocal-mass topology into Hilbert--Schmidt topology after the selected
divisor has been normalized to one fixed reciprocal spectral coordinate.

Scope is exact. It does **not** rule out an arithmetic-discontinuous or non-Hilbert--Schmidt source
assignment. It does not infer Hilbert--Schmidt continuity from source naturality; that implication must be
proved for any proposed producer.

## Gates

- [x] 0 → 1  in-progress: well-posed fixed-coordinate operator claim; source application scoped
- [x] 1 → 2  fully-proven: complete paper proof below, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: determinant-continuity and Beurling-firewall leaf builds green; lint and axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper

## Status and novelty

`[REDISCOVERED BRIDGE]`, not a new functional-analytic theorem. Classical Hilbert--Carleman
determinants are defined on the Hilbert--Schmidt class by continuous extension from finite-rank
operators. Novelty claim is only corpus-specific use as a firewall between reciprocal source topology
and divisor-moving operator descent.

## Paper proof `[PROVED HERE]`

Let `K_n` and `K_0` be Hilbert--Schmidt kernels and suppose
`||K_n-K_0||_HS -> 0`. Fix `z in C`.

1. Triangle inequality gives an eventual common bound `||K_n||_HS <= M`, with
   `M = ||K_0||_HS + 1`.
2. Choose `r > 0` with `r M < 1`, and choose `0 < rho < r`. On the closed `rho`-disc the
   disc-local exponential representatives satisfy the corpus estimate

       sup_{|w|<=rho} |fredholmDet(K_n,w)-fredholmDet(K_0,w)|
         <= C(M,r) ||K_n-K_0||_HS.

   Cauchy's coefficient estimate therefore implies convergence of every Taylor coefficient at zero:
   `detCoeff(K_n,k) -> detCoeff(K_0,k)`.
3. The Carleman coefficient estimate is uniform on the same Hilbert--Schmidt ball. For every `R>0`,

       |detCoeff(K_n,k)| <= exp(R^2 M^2/2) / R^k

   eventually, and the same bound holds for `K_0`. Taking `R=2|z|` when `z != 0` turns the
   coefficient terms at `z` into a fixed summable geometric majorant. Dominated convergence of the
   Taylor series gives

       entireDet2(K_n,z) -> entireDet2(K_0,z).

   At `z=0`, every determinant equals one, so the conclusion is immediate.
4. If `entireDet2(K_n,z)=0` for every `n`, uniqueness of limits forces
   `entireDet2(K_0,z)=0`. Therefore this persistent-zero family cannot coexist with a nonzero limiting
   determinant.

This proves the theorem.

## Source application and survivor

Normalize each source-selected moving divisor into its operator kernel so that it is tested at spectral
coordinate `z=1`. If reciprocal perturbation size tends to zero, a candidate source-natural producer
lands continuously in Hilbert--Schmidt norm, and every perturbed determinant vanishes at `1`, then its
base determinant must also vanish at `1`. The small-mass Beurling off-line perturbations make this a
firewall against any such topology-respecting universal divisor encoder.

**Strongest survivor:** a viable arithmetic producer must fail at least one of:

- fixed-coordinate coefficient-faithful divisor encoding;
- reciprocal-to-Hilbert--Schmidt continuity;
- Hilbert--Schmidt target class.

Arithmetic discontinuity is therefore a mathematical obligation, not a free escape phrase: a proposed
producer must identify and prove the exact discontinuous source invariant.

## External audit

- Britz--Carey--Gesztesy--Nichols--Sukochev--Zanin, *The product formula for regularized Fredholm
  determinants*, arXiv:2007.12834: standard Hilbert--Schmidt `det_2` framework.
- Classical construction extends finite-rank Hilbert--Carleman determinant continuously to the
  Hilbert--Schmidt class; no corpus-specific reciprocal-topology firewall was found.

## Log

- 2026-08-17 — statement frozen after rejecting the vacuous disc-local `fredholmDet` formulation:
  that local exponential never vanishes. Correct target is canonical entire continuation `entireDet2`.
- 2026-08-17 — paper proof closed by local Lipschitz + Cauchy coefficients + global Carleman domination.
- 2026-08-17 — formalized in `EntireDet2HilbertSchmidtContinuity.lean` and
  `BeurlingReciprocalOperatorFirewall.lean`; exact leaf builds, formal lint, and axiom audit PASS.
