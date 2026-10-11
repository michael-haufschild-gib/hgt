# Standard square-root normalization of cubic-cluster mass

Status: formalized; native build and complete axiom/API audit passed.
Date: 2026-10-10. Local corpus only.

Formalized predecessor: `finite-weil-cubic-mass-limit.md` identifies the limit S_r/sqrt(m_r)->sqrt(pi), with m_r=floor(r/2)+1 and cubic start k_r=2(r+1)³. This follow-up removes the parity normalization from the final statement.

Set n_r=r+1. Natural-number division gives 0<=2m_r-n_r<=1. Dividing by 2n_r>0 gives 0<=m_r/n_r-1/2<=1/(2n_r), so m_r/n_r->1/2. Continuity of the real square root gives sqrt(m_r/n_r)->sqrt(1/2).

Since m_r,n_r>0, the exact identity S_r/sqrt(n_r)=(S_r/sqrt(m_r))*sqrt(m_r/n_r) holds. Multiply the predecessor limit and the ratio limit above, and use sqrt(pi)*sqrt(1/2)=sqrt(pi/2). The target is the unconditional limit S_r/sqrt(r+1)->sqrt(pi/2) for the same explicit cubic start sequence.

No numerical fitting, external asymptotic input, or analytic hypothesis. The only asymptotic input is the corpus's Wallis limit already transferred by the predecessor.

Completed in `WeilLogShiftStandardMassLimit.lean`: sharp half-order ratio error (line9), ratio limit (line31), exact change of normalization (line40), standard arithmetic mass limit (line49), and standard cubic logarithmic mass limit (line60). All five declarations are unconditional.

Shared verification with the polynomial/variable-degree companion: three native leaves exited0 with empty logs; `/tmp/hgt-standard-expanded-audit.lean` checked all 13 public declarations and 7 explicit API terms. All axioms are contained in `propext`, `Classical.choice`, `Quot.sound`. Metadata audit found no source/direct-dependency freshness, complete-axiom-coverage, or exact-umbrella-count issue. Exhaustive incoming imports are the umbrella and internal chain. One owned Lean process at a time; no full/umbrella build or heartbeat increase.

First native pass found a redundant `ring` after `field_simp` had closed the ratio identity; removing it gave the clean final build. No mathematical weakening.

Final formal lint `/tmp/hgt-standard-final-lint.log` exits1 on five unrelated missing umbrella imports: `RHTower.JointAncestryLogWeightBernoulli`, `RHTower.JointAncestryLogWeightPrimeSum`, `RHTower.XiCosineShiftExceptionalPointIndex`, `RHTower.XiGaussianHeatHankelDeterminantSignLaw`, `HTGeometry.QKrawtchoukCompanionTriangular`. No errors in authored leaves; foreign work untouched.

Stronger completed follow-up: `finite-weil-polynomial-mass-limit.md` proves the same constant for every degree at least three, even when the degree varies arbitrarily with order.

Local index refresh and exact final-root lookup for the arbitrary-degree-function companion passed. All owned native processes are terminal.
