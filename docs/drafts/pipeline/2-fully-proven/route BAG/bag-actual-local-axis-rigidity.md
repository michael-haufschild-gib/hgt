# BAG actual local axes rigidity and complete nonzero-channel removal

Paper proof, continuation01al. Route: complete signed physical prime cubic.
All statements concern the actual plateau Schwartz family from ag.18;
no assumed cancellation, RH, Fourier-norm bound, or discarded cofactor.

For a prime label r in the physical band (N,2N], write E_r for the full
excluded complementary-prime source. Its local r-coordinate factor is the
base with Fourier multiplier 1-1_(r|n). Replace that factor by a point mass
at zero, retaining every other prime coordinate and every distinguished
label p!=r. On the actual positive Fourier band n<=2N<2r, either r does
not divide n, in which case both r multipliers equal1, or n=r. In the
latter case every remaining distinguished tag p!=r has zero multiplier.
Hence the original and pinned COMPLETE sources agree on every physical
mode. The exact finite expansion of the entire physical-height test then
proves invariance under either pin separately and under both pins together.

Let B_r denote the full excluded inverse-profile action, including all
complementary factors and both physical exclusions. The exact zero-defect
axes/intersection formula is

  A_r = (1-1/r)(B_r+B_r) - (1-1/r)^2 B_r = (1-r^-2) B_r.

The complete pairing is B_r=A_r+K_r. Thus the entire nonzero inverse-fibre
channel is K_r=r^-2 B_r. No single-fibre estimate or independent profile
hypothesis is used. The original initial all-row-average conjecture is
stronger than needed and is NOT claimed as a formalized theorem; the
proved pinning identity is the exact sufficient positive survivor.

To show this removes a whole channel at the required scale, recover the
actual physical row by the excluded source's covered-band Fourier law:

  log(r) B_r = sum_{p,q in physical prime band; p!=r,q!=r}
    eta(p) eta(q) eta(r) MainEntry(N,p,q,r).

The amplitudes lie in [0,1]. The existing physical entry bound 8/N and
integer-band cardinality <=2N give row norm <=32N. Since r>N, the complete
nonzero row has norm <=32/N. All labels outside the physical band contribute
zero by the actual third-coordinate support. There are at most3N covered
prime labels for N>=2. Hence the COMPLETE summed nonzero action has norm
<=96, uniformly in N. This constant is incidental; the conclusion is
log(N)^2/N times that norm tends to zero. Combine the exact full split with
the already proved sharp-minus-full-action error and the triangle inequality:
the original sharp signed cubic differs from the COMPLETE axes action by
o(N/log(N)^2) in complex norm.

No-go and positive survivor: nonzero local inverse-fibre cancellation alone
cannot prove the cubic saving, because the axes retain the full correlation
up to this negligible error. The survivor is an unconditional actual-family
reduction to the complete axes action. This does NOT identify all physical
near-cone/tail regions with nonzero local product-defect fibres. It does NOT
prove the axes saving, a growing moment estimate, or RH. BAG remains open.
The next hard target is the signed sum of these actual axes values across
all physical prime heights, with its entire growing complementary source.

Lean status: both ChiPrimeGaussianCubicLocalAxisRigidity and
ChiPrimeGaussianCubicLocalAxesReduction passed final leaf production and
all23 new/exposed public declarations passed standard-axiom audit. Full
nonzero-channel removal and the unconditional family reduction are proved;
see P3/bag-actual-local-axis-rigidity.md for validation details.
