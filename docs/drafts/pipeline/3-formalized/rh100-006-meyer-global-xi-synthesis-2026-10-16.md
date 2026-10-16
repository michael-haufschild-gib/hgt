# Contribution 006: global Xi synthesis in the literal Meyer source

Status: formalized and directly audited. Ledger 6 / 100. Contribution 005
removed invisible finite-word torsion. This contribution eliminates the
entire invisible sector and proves global source-native Xi synthesis.

Scope: seek a distinct hard structural advance using multiple current corpus
routes. Finite resolvent corollaries of 005 do not count. Initial searches
compare full spectral synthesis, heat/Hankel source structure, and natural
Frechet topology. Read actual Lean statements before choosing a conjecture.

Plan: inspect current frontier and search hits; formulate and attack competing
exact conjectures; complete a dependency-closed paper proof; formalize only
the surviving substantial result; audit leaves, axioms, imports and lint;
clean owned scratch and record precise scope.

User overrides to hgtl7: no external search or novelty audit, no old research
reports, no numerical experiments. No extra premises, axioms, proof holes,
heartbeat increases, full builds, or umbrella builds. One owned foreground
Lean process at a time. Preserve concurrent research edits.

Boundary at entry: invisible polynomial torsion vanishes, but the whole
invisible sector may still be nonzero. Empty Frechet spectrum alone does not
justify vanishing. Infinite-packet synthesis and positive source forms remain
unresolved. A source-adapted weighted synthesis space defined only by the
norms of existing sections would risk being a routine receiver rather than a
new structural advance.

## Surviving conjecture and paper proof

Target: the literal Meyer-to-compact-open-Xi comparison is injective.
Equivalently, its entire jet-invisible sector is zero. This is not full
packet surjectivity and makes no positivity or RH assertion.

The direct Mobius approach exposes a missing origin-regularity argument:
all nonnegative L1 moments alone do not supply smoothness at zero. Shifting
only to Re(s)=-1 also does not supply it. No such inference is used.

Instead combine the genuine closed Poisson range and exact Xi cap (HF),
good horizontal Xi ratios and the Gamma floor (theta-divisibility/Burnol contour input),
and Gaussian heat regularization (TH/HCF mechanism). Write S for the
all-weight logarithmic source and N for its actual Poisson range.

1. For g in S with every Xi jet zero, global entire division gives
   M(g)=xi*H, H entire. M(g) is bounded and rapidly decreasing uniformly
   on every closed vertical strip: integrate by parts in logarithmic
   radius and use the all-weight derivative bounds.
2. The Gamma floor on Re(s)>=2 and reflection on Re(s)<=-1 bound H
   exponentially in |Im(s)| on each fixed exterior vertical line.
   Burnol's good-height ratios transfer the bound across [-1,2] with a
   fixed polynomial height loss. Maximum modulus on good rectangles
   yields, for every A, constants B,C with
   |H(s)|<=B exp(C|Im(s)|) for |Re(s)|<=A. Constants may depend on A;
   no global exponential type in the horizontal direction is asserted.
3. For epsilon>0, H_epsilon(s)=exp(epsilon*s^2) H(s) decreases faster
   than every vertical power on each closed strip. Its inverse bilateral
   Laplace transform h_epsilon lies in S. Proof: all vertical moments
   give smoothness; shift the inverse integral for the n-th derivative
   to Re(s)=+/-A to get arbitrary exponential decay. Ordinary Fourier
   inversion gives M(h_epsilon)=H_epsilon. This uses zeroth-order strip
   bounds and contour shifts, not an unproved derivative bound on H.
4. Average dilates of the fixed Xi cap against h_epsilon. Derivatives
   and polynomial Schwartz weights cost only exponential powers of the
   dilation parameter, absorbed by h_epsilon. Differentiation and Fubini
   therefore produce an actual even Schwartz cap with both endpoint
   conditions, whose Poisson Mellin transform is xi*H_epsilon.
5. These actual boundaries converge to g in the original source topology.
   On Re(s)=k, inverse Fourier bounds the weighted n-th derivative of
   the difference by the L1 norm of
   (-s)^n*(exp(epsilon*s^2)-1)*M(g)(s). For 0<epsilon<=1, the exponential
   factor is bounded by exp(k^2)+1; rapid vertical decay supplies an
   integrable majorant. Dominated convergence gives every source gauge.
6. N is closed in this topology, hence g belongs to N. The invisible
   kernel is zero. This justifies faithful infinite-dimensional
   arithmetic calculus on the actual observable image, without claiming
   arbitrary packets are admitted.

Paper dependency audit: each analytic operation above has an explicit
majorant and a specified topology. All six steps are formalized and form
one contribution; none is counted separately.

Formal result: direct leaf audits passed Mellin reconstruction, uniform
source strip control, Gaussian strip regularization, Xi quotient growth,
Schwartz dilation averaging, cap endpoint/Fubini multiplication, and Gaussian
removal in the natural source topology. The final closed-range synthesis
theorem and its whole-cohomology faithfulness consequences passed as well.
All eight leaves are wired into the RHTower umbrella.

## Exact structural change

`deningerMeyerXiSpectralSynthesis` proves the existing source-native synthesis
property outright. `deningerMeyerInvisible_eq_bot` eliminates the entire
comparison kernel, not only finite-word torsion. Consequently full arithmetic
jets separate every literal cohomology class, and the arithmetic causal
projector is the identity on the whole quotient.

The mechanism is regularize the quotient, realize its product with Xi as an
actual cap boundary, and remove regularization in the original source
topology. Division itself need not preserve the source's rapid vertical
decay. Fixed-strip exponential control suffices because Gaussian inversion
and closed Poisson range supply exact admission after taking the limit.

This enables faithful source reconstruction and arithmetic operator
identification for arbitrary existing classes, including classes outside
every finite causal sector. It does not admit arbitrary prescribed infinite
jet packets, give a continuous inverse to the compact-open comparison, or
produce a positive Hodge form. RH remains unresolved.

## Corpus inputs and formal outputs

HF actual-source inputs: `deningerMeyerXiCapSource_mellin`,
`deningerMeyerStrongLog_boundary_limit`,
`deningerCompactOpenXiRange_eq_allJets_ker`, and faithful entire source Mellin.
Theta-divisibility/Burnol contour inputs: `xi_floor`, `xi_floor_two`,
`exists_xi_horizontal_ratio_nat_bound`, `norm_quotient_le_horizontal`, and
`norm_le_of_rectangle_frontier_bound`. Strip Mellin inversion and Fourier
inversion connect those source and contour routes. Gaussian regularization
is proved here with complete all-weight source convergence.

Eight new leaves, all directly checked with `lake --old env lean`:

- `DeningerMeyerMellinReconstruction`: reconstruct actual all-weight sources.
- `DeningerMeyerMellinStripControl`: genuine source Mellin regularity.
- `DeningerMeyerGaussianStripRegularization`: invertible Gaussian regularization.
- `DeningerMeyerXiDivisionGrowth`: entire quotient control on every strip.
- `DeningerMeyerDilationAverage`: all Schwartz seminorms of physical averages.
- `DeningerMeyerDilationCapAverage`: endpoint cancellations and Mellin product.
- `DeningerMeyerGaussianSourceApproximation`: convergence in original topology.
- `DeningerMeyerGlobalXiSynthesis`: global source admission and zero invisible sector.

## Final audits

All eight direct foreground leaf checks exited zero using
`lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<Module>.olean GaloisForLFunctions/RHTower/<Module>.lean`.
No full or umbrella build ran. Eighteen declarations were audited in a `/tmp`
scratch file; every dependency list was exactly `propext`, `Classical.choice`,
`Quot.sound`. No added axioms, proof holes, numerical experiments or heartbeat
changes were used. Owned temporary searches and scratch files were removed.

Repository `scripts/formal_tools.py lint` completed with one unrelated
concurrent failure: `GaloisForLFunctions.RHTower.CHMDClosedJumpGraph` was
unreachable from its umbrella. All eight new Meyer leaves are wired. The
concurrent CHMD module was left unchanged. Existing large-file warnings also
remain. The theorem audits are clean; repository-wide lint is not claimed clean.
