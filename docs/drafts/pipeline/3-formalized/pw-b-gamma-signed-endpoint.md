# PW-B literal Gamma signed endpoint and reconstruction defect

- **ID:** PW-B-GAMMA-SIGNED-ENDPOINT-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** The actual zero-parameter Gamma/Möbius preimage is globally integrable on the positive ray, with zero mass and strictly positive finite `L¹` norm. Its arithmetic reconstruction is the original integrable Gamma source. Reconstruction has exact series/integral defect `Gamma(3/2)>0`, although each positive dilation of the preimage has zero mass.

## Actual source and signed admission

Keep `Q(x)=sqrt(x)*exp(-x)` for `x>0` and the original source
`M(x)=sum_n mu(n)*Q(n*x)`. The measure is Lebesgue `dx` on `x>0`.
The [absolute-admission theorem](pw-b-gamma-global-absolute-admission.md)
proves that the original sum of atom norm integrals fails at coefficient
parameter zero. It does not decide integrability of the signed sum.

The new assembly retains the original Möbius partial sums
`S(n)=sum_(j<=n) mu(j)` and defines

`B_n(x)=S(n)*(Q(n*x)-Q((n+1)*x))`.

The zero index is zero. The exact finite identity, valid before any limit,
is

`sum_(n<N) B_n(x) = sum_(n<=N) mu(n)*Q(n*x)-Q(N*x)*S(N)`.

The terminal term is explicitly proved to tend to zero for each `x>0`.
The known inverse-square Gamma bound and `|S(N)|<=N+1` give a constant
multiple of `1/N+1/N^2` as a vanishing majorant. The original source series
and the Abel series are both proved summable pointwise; uniqueness of limits
gives the exact equality `M(x)=sum_n B_n(x)`.

## Literal Gamma difference bound

For every positive real `r,x`, direct factorization gives

`|Q((r+1)*x)-Q(r*x)| <= (1/r+x)*Q(r*x)`.

The square-root increment is bounded by `sqrt(r)/r`; the exponential
increment uses `0<exp(-x)<=1` and `1-exp(-x)<=x`. No stronger Schwartz
membership or differential-domain premise is introduced.

The two exact Gamma moments are

`integral Q(x) dx = Gamma(3/2)` and
`integral x*Q(x) dx = Gamma(5/2)`.

Positive dilation, with its Jacobian retained, therefore gives

`integral |Q((r+1)*x)-Q(r*x)| dx <= (Gamma(3/2)+Gamma(5/2))/r^2`.

The current corpus's unconditional theorem
`deningerMertensM_invSq_summable` proves `sum |S(n)|/n^2<infinity`.
Thus **the new Abel atoms have summable `L¹` norms**, and their actual sum
is integrable. This proves `M in L¹(dx)` at the endpoint where the original
atom norm sum diverges. The arithmetic saving is PNT-strength, not an
assumed RH or square-root bound.

## Exact zero mass and nonzero source

Each Abel atom is integrable, and its integral is exactly

`integral B_n(x) dx = Gamma(3/2)*S(n)/(n*(n+1))`.

The admitted interchange converts the complete integral into the signed
harmonic Möbius limit times `Gamma(3/2)`. The corpus already proves that
limit is zero, using the zeta pole and a justified Abelian limit. Hence

`integral M(x) dx=0`.

The original arithmetic reconstruction proves `M` is not identically zero
on the positive ray. The new reconstruction argument below strengthens
this to `integral |M(x)| dx>0`, so `M` represents a nonzero `L¹` class.
Zero mass is a complete signed cancellation, not a zero source.

## Reconstruction retains a nonzero boundary defect

Let `Z M(x)=sum_(n>=1) M(n*x)`. The previously proved actual-source identity
is `Z M=Q`. Consequently `Z M` is integrable and

`integral Z M(x) dx=Gamma(3/2)>0`.

But every positive dilation of `M` has integral zero by the dilation
Jacobian and the proved zero mass. Therefore the exact defect is

`integral sum_(n>=1) M(n*x) dx - sum_(n>=1) integral M(n*x) dx = Gamma(3/2)`.

The reconstructed sum and every summand are integrable; nevertheless the
sum of their norm integrals cannot be summable. Otherwise the Bochner
interchange theorem would contradict this positive defect. If `integral
|M|` were zero, all those dilation norm integrals would vanish and would be
summable, giving the same contradiction. This proves the strict positive
`L¹` norm asserted above.

## Route scope and next obstacle

Literal PW response -> FE partner imbalance -> positive Deninger Ward
transmutation -> independently source-forced fixed-grade balance -> RH
remains the chain. This result closes a genuine source-domain obligation
at coefficient parameter zero and identifies a nonzero contribution in
the complete arithmetic reconstruction. A Ward argument must retain that
contribution; integrability of input and output does not justify removing it.
RH remains unproved and PW-B stays active.

The successor [actual logarithmic-current audit](pw-b-gamma-logarithmic-current.md)
now admits `E=partial_b M_b|0` globally and proves `integral E=Gamma(3/2)`.
Its logarithmic Abel assembly retains both terminal terms and all integral
interchanges. The complete Euler current has the same nonzero defect,
and `E-Q` is an admitted zero-mass difference. This still leaves the
physical measure, complete differential forcing and spectral parameter
identification before any Ward balance conclusion.

No global parameter derivative, negative-parameter power gain, critical
finite energy or spectral Ward parameter identification follows from the
present endpoint. Extending signed admission toward the RH-relevant region
requires stronger arithmetic cancellation, not a relabeling of zero mass.

## Method and novelty audit

Four partial-coverage deep searches and their candidate/method metadata are
saved in [search artifact](../1-in-progress/pw-b-gamma-signed-endpoint-searches.json).
The source methods are the existing finite Abel identity, inverse-square
Mertens summability, Gamma integrals, positive dilation, harmonic limit,
and Bochner-series admission. Earlier Deninger preimage theorems retain a
stronger source-class premise unavailable for the literal Gamma profile.
The present proof replaces it with a verified direct Gamma difference
bound and preserves the actual reconstructed source. This is an exact
source extension and defect audit, not a claim of a new general Abel theorem.

Broad recent searches inspected [viscoelastic adhesion](https://arxiv.org/abs/2607.08213)
(July 9) and [target fragmentation](https://arxiv.org/abs/2609.03368)
(September 3). Their model-specific constitutive laws and physical channel
assembly supply no arithmetic endpoint theorem under the hypotheses proved
here. No external theorem or numerical experiment enters the proof.

## Formal surface and validation

Leaf: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekGammaMobiusSignedEndpoint.lean`.
Twenty-two public theorems and one definition. The closed
`pwGammaMobiusSignedReconstruction_closed` packages actual integrability,
zero mass, nontriviality, positive `L¹` norm, reconstructed integrability
and mass, all positive-dilation zero masses, and the failure of absolute
reconstruction norm summability.

Validation completed:

- Scratch and direct leaf checks passed with `lake env lean <file>`.
- Final audit used only `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaMobiusSignedEndpoint`; target compiled in 99 seconds, with dependency jobs replayed from cache.
- All 22 public axiom audits passed in `/tmp/pwb-gamma-signed-axioms.lean`; only `propext`, `Classical.choice`, `Quot.sound` occur.
- Formal lint passed. Index regenerated all three formal ledgers and records 22 theorem rows and one definition row.
- All 23 public names are unique. Task-scoped diff and new-file whitespace checks passed.
- Umbrella import wired. No full/umbrella build or numerical experiment ran. All owned Lean and research processes finished.

Logs: `/tmp/pwb-gamma-signed-{scratch,direct,build,axioms,lint,index}.txt`.
