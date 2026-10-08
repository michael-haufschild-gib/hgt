# Differential synthesis width: cycle 15

Status: paper proof and final Lean leaf audit complete. Imported-cache axiom/global-lint checks recorded in EVIDENCE.md. Main WP02 receiver OPEN.

## Exact result under audit

Let Phi be the literal Riemann kernel, fix a finite list of derivative orders k_j, and set

    f_c,x(t)=sum_j c_j Phi^(k_j)(t-x_j),  M(c)=sum_j |c_j|.

Coefficients are arbitrary complex numbers. For every real R and 0<a<pi, there is C>0, depending only on the derivative list, R and a, such that simultaneously for all c, all positions |x_j|<=R, and all integers n>=1,

    |atomCoeff(f_c,x,n)| <= C M(c)^2 exp(-2*a*exp(-2R)*n).

For R<1, consider any finite signed mixture T(n)=sum_i alpha_i atomCoeff(f_(c_i,x_i),n), with every row's translations lying in a window of radius R around its own arbitrary center. Its homogeneous coefficient budget is

    S=sum_i |alpha_i| (sum_j |c_ij|)^2.

There are C,delta>0 such that eventually |T(n)|<=C*S*exp(-delta*n)*exposingWeight(n), uniformly over the mixture data. Consequently |T(n)|>=exposingWeight(n) forces exp(delta*n)<=C*S. Every fixed mixture is negligible against the literal exposing ray and cannot equal any nonzero fixed multiple of that ray on all sufficiently large integers. The factor 2*pi in the dual trace convention can be absorbed into the arbitrary mixture weights.

## Positive survivor and scope

The quantitative decay and amplification laws are the positive survivor. They constrain moving coefficients and translation positions in a fixed finite derivative basis, rather than merely excluding one odd source. Width two is the first possible boundary for fixed-source literal exposing-rate production. The existing literal unit-shift source has that translation width. Exact coefficient matching at the boundary is a separate constructive question, recorded in CRITICAL-WIDTH-ODD-CONJECTURE.md.

The source class includes the polar derivatives D^k(D²-1/4)Phi by finite linear expansion, and includes arbitrary finite translation filters of Phi itself. An arbitrary packet is neither asserted polar nor compact. The tail theorem needs neither assertion and no analytical positivity premise.

[OPEN CORE] Produce exact opposite-ray families with complete trace and required signed energy. This result does not exclude derivative orders growing with the cutoff, translation width >=2, or arbitrary compact polar tests. It supplies no archimedean lower bound.

## Hostile and novelty audit

All complex cross terms are controlled through the norm of the entire synthesized source. Both tails and actual symmetrized integer samples are retained. Exposing weights are used as positive only after their proved eventual positivity threshold. Translation radius is not compact support radius. Strict width <2 must not be replaced by <=2.

The budget S is invariant under compensating test/weight rescalings, but remains a representation budget. Clustered positions can create large cancelling coefficients. Amplification does not imply large energy or a large intrinsic spectral norm.

Novelty verdict: a corpus-specific source-class boundary and quantitative synthesis constraint, not a new general asymptotic method or RH proof. The documented corpus queries and metadata limitations are recorded in EVIDENCE.md. Primary comparison: Csordas, *Fourier transforms of positive definite kernels and the Riemann xi-Function* (2014), https://arxiv.org/html/1309.0055v2. Its inspected kernel/Laguerre framework does not supply this literal exposing-weight comparison. Partial retrieval does not certify absence.
