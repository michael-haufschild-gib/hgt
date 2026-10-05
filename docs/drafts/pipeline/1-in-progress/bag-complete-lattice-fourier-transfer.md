# BAG complete physical lattice Fourier transfer

- Continuation: 01ab; parent C28.56ag.5.
- Route: complete signed physical BAG cubic.
- Status: full Poisson and complete critical atom/projector matching formalized;
  signed growing cancellation remains open.
- Parent: bag-complete-hyperbolic-transition-action.md.

The exact continuum transition is audited. Next conjecture: the actual
smooth compact THREE-coordinate amplitude has an absolutely summable full
lifted Fourier family, and its full integer sum equals that family. Keep
the r-coordinate, every integer lift, both literal contractions and the
critical finite atom tensor. The target after this transfer is the signed
o(N/log(N)^2) estimate, not absolute convergence alone.

Write f(p)=eta(p)*V(p/N)/log(p). The physical amplitude is

    A(p,q,r)=2*pi/r * f(p)*f(q)*conj(f(r)) *
       W(p*q/(r*N))*e(p*q/r).

All three coordinates have the actual eta support in (N,2N). The
zero-neighborhood at r<=1 removes the division singularity. Actual V and W
smoothness and compact support must be proved, not supplied as assumptions
for the final family. Standard Euclidean Schwartz Fourier decay should
give absolute lattice summability. A proof of multidimensional Poisson is
still needed; repeating 1D formulas without exchanges is insufficient.
The corpus's multidimensional torus Fourier convergence and fundamental
domain integration provide a possible complete proof mechanism.

Search83657 completed with partial=true only because reranking hit its
local deadline; inventory65691/65691 complete, refresh incomplete under
background indexer, compiler mostly source_only/pending. All20 candidate
and20 source statements/method summaries, empty proof ideas and proposed
ingredients inspected. The proposed bandlimited Nyquist premise is not
valid for this amplitude; applicable Fourier-Schwartz decay, 1D Poisson,
multidimensional torus convergence and fundamental-domain APIs were read
directly. No conclusion follows from missing search hits.

This construction does not yet solve signed cubic cancellation. The
subsequent hard problems remain the complete near-cone/tail action,
growing moments, moving cofactors, common-height self-return and RH.

## Actual three-coordinate construction

The next substatement is formalized, with paper and audit records in P2/P3:
bag-full-physical-fourier-lattice-summability.md. The production leaf is
ChiPrimeGaussianCubicFourierLattice. It constructs the actual A, proves global
smoothness across r=0 using the cutoff's zero neighborhood, proves compact
support in all three coordinates, checks the literal natural coefficient,
and proves absolute Fourier sampling at EVERY real three-frequency shift.
The final existential family has no hypotheses and preserves the previous
sharp/smooth comparison. It supplies no bound uniform in growing N.

This avoids an unnecessary sum/Mellin interchange: transform the whole
physical amplitude first and prove summability of the resulting integrated
coefficients. One may later retain each coefficient's nested Mellin
representation without claiming absolute interchange with all lattice
lifts. Actual multidimensional Poisson matching is still pending.

Lexical window-smoothness search87974 returned no declarations; direct
source inspection identifies the actual W as ContDiffBump, whose contDiff
is already used in ChiRamanujanDampedSquareMellin. Missing hits were not
treated as mathematical absence. API probe6933 passed after fixing
universe-polymorphic probes. Development corrections so far: provide the
norm/absolute-value sign facts in the lattice majorant; open the literal
window namespace; make compact-cube pullback explicit; unfold composition
as a function; use map_div₀ for complex conjugation of total division and
keep real logarithms from being rewritten to complex ones.

## Final checkpoint — C28.56ag.5

Development17343, production19066 and all12-name axiom14865 passed without
diagnostics; only standard Lean axioms. Index92591 passed, all12 API names
present, umbrella import once. Lint13216 reports28 unrelated unreachable
modules only; global lint is not clean. All owned jobs terminal and completed
scratch sources removed. The next task is actual full Poisson matching,
retaining all lifts and finite literal actions. No signed saving follows.

Concretely, for every actual good scale and every a in Euclidean three-space,
prove the complete twisted integer sum of A equals the absolutely convergent
sum of hat(A)(k-a) over ALL k in Z^3. Compact support makes the physical sum
finite. Periodization, full multidimensional Fourier coefficients and the
already available torus Fourier convergence offer a proof path; no
multidimensional Poisson theorem is yet asserted. After matching, use finite
linearity to retain the exact critical atom tensor and BOTH contraction
projectors. The difficult source-specific signed bound is still open.

## Continuation 01ab — complete Poisson matching

Route unchanged: prove full compact-amplitude Poisson by continuous integer
periodization on the three-torus, identify every Fourier coefficient by
fundamental-domain unfolding, then use the already proved all-shift absolute
Fourier summability. Preserve the actual amplitude and both contractions.
This is a necessary exact matching step; it supplies no signed cancellation.
Search66852 is terminal: partial reranking deadline, full65700/65700 source
inventory, background refresh incomplete, compiler mostly pending/source-only.
All20 candidate and20 source statements, empty proof ideas and proposed
ingredients inspected. Open-unit-cube support is NOT available for our growing
physical support, so the suggested at-most-one-translate shortcut is invalid.
Use compact support to obtain locally finite translates, allowing overlap.

The compact periodization mechanism passed development94244 and production
leaf audit51112 (exit0, empty logs). ChiCompactLatticePoisson is wired once.
This establishes the complete integral-coefficient Poisson identity, with
absolute coefficient summability as a generic input. The actual-family
consumer now being checked must discharge that input, identify Euclidean
Fourier normalization/sign and retain arbitrary shifts. No final BAG Poisson
family is asserted until that check succeeds.

Physical Poisson leaf production11522 passed, exit0/empty log. The complete
all-shift formula and unconditional physical family now pass Lean. Sign and
normalization were checked through volume-preserving coordinate conversion
and the exact character identity. Both leaves are wired once. Axiom/index/lint
audit remains pending while the full critical-atom/projector consumer is built.

Next conjecture: the lifted Fourier function equals the literal finite
unmasked smooth physical cube test; its critical atom action under BOTH
projectors therefore equals the smoothed signed cubic exactly. Prove zero
outside the physical natural band before replacing the full integer sum.
Search17413 partial (decomposition deadline), complete65707/65707 inventory,
background refresh incomplete; all20+20 statements and generated proposals
inspected. Those lattice/recurrence proposals do not supply our finite-band
identity. Targeted lexical fallback returned the two exact definitions; both
source bodies and the existing projected-cube theorem were read. No new
arithmetic premise or damping limit is needed for this exact matching.

## C28.56ag.6 — completed mathematical checkpoint

Both next conjectures are proved: full all-shift Poisson, then complete
critical atom/projector matching. Three leaves /12 public declarations;
production51112/11522/58567 and axiom11043 passed, with only standard axioms.
Index18738 passed and all12 entries are present in LEAN_API (short names
within module rows); each new umbrella import occurs once. Lint56265 reports31 unrelated unreachable
modules only; no new-leaf/proof-debt errors. Global lint is not clean.
The exact signed action is now ready for the hard near-cone/tail estimate;
no uniform N estimate, signed cubic saving or downstream RH producer exists.
See the next conjecture in bag-complete-hyperbolic-transition-action.md:
retain the full r/Mellin transition and expose zeta+xi*upsilon before the
source-specific cancellation attack. Goal ACTIVE.
