# RN-P-7e: actual two-node Schur single-zero barriers

Status: conjecture, not proved. Route RN. No Lean statement in this card is
claimed to establish three-node or arbitrary-rank tail positivity.

For the literal theta source `k` and first-moment kernel `H`, fix
`0≤x₁<x₂<y`. Put `M=(H(xᵢ,xⱼ))`, `hᵢ=H(xᵢ,y)`, `c=M⁻¹h`,
`uᵢ=k(xᵢ)`, `vᵢ=xᵢk(xᵢ)`, `α=uᵀM⁻¹u`, `γ=vᵀM⁻¹v`.
The unconditional two-node determinant theorem guarantees invertibility.
Define

    A=k(y)-Σ cᵢk(xᵢ), B=y k(y)-Σ cᵢxᵢk(xᵢ),
    W=k'(y)-Σ cᵢk'(xᵢ), C=y k'(y)-Σ cᵢxᵢk'(xᵢ).

Conjectured actual-kernel barriers:

    A=0, B>0  ⇒  W+αB<0,
    B=0, A>0  ⇒  C+(1+γ)A<0.

These are the remaining two nonzero-axis entries for the common-shift
Schur flow. The exact paper identities are
`A'=W+βA+αB`, `B'=C+(1+γ)A+βB`, `S'=-2AB`, with
`β=uᵀM⁻¹v`. Far-tail initialization, local crossing orientation and the
whole continuation argument must all be retained; these barriers alone
are not an RH proof.

What has advanced:

- `ThetaTailOrderedRowMonotonicity` proves `L(x,·)` strictly decreases on
  `[x,∞)` for `x≥0`, where `L=H/(k k)`.
- `ThetaTwoNodePortTransversality` proves both free derivatives negative
  at simultaneous port zeros. The coefficient-elimination and source
  inequalities passed the targeted build, standard-axiom audit and final
  direct leaf audit; the module is wired into the umbrella.
- Uniform row convexity/concavity is false. Scalar row decrease does not
  sign the coupled drop determinant
  `(L11-L12)(L22-L2y)-(L12-L22)(L12-L1y)`.

Next proof attack: retain both actual projection equations `Mc=h` and
their common-tail integral representation when comparing the negative
free derivatives with `αB` and `(1+γ)A`. Merely dropping these positive
feedback terms proves the wrong statement. Do not assume a source-only
upper bound on the inverse-matrix terms.

Search audit: `theta kernel Wronskian` found a full-Xi/full-density phase
Wronskian no-go, not a translated-tail comparison. `curvature Turan`
found the actual fourth-reflection law
`160<ℓ''''+4(ℓ'')²` and moment identities, neither of which directly
controls the projection terms. This is not evidence that no suitable
corpus theorem exists; lexical coverage is not a proof of absence.

Higher rank: the two port-zero equations determine two coefficients only
when there are two earlier nodes. Any extension must use actual projection
equations to control the remaining coefficient freedom.

## Exact forcing law found in the next conjecture loop

Put `s=(p₂-p₁)/(x₂-x₁)`, `j=(x₁p₂-x₂p₁)/(x₂-x₁)`,
`t=(x₂p₂-x₁p₁)/(x₂-x₁)`, `r=x₁x₂s`. Let `E,F>0` be the
strict extrapolation defects of `p` and `x p(x)` at y. Then

    W=jA-sB-k(y)E, C=rA-tB-k(y)F.

Consequently the two actual barriers reduce exactly to

    (α-s)B < k(y)E  at A=0,B>0,
    (1+γ+r)A < k(y)F  at B=0,A>0.

The first negative free derivative extends to the whole `A=0,B≥0` axis.
The second does not: for every strictly positive earlier-node pair there
are source-port coefficients with `A>0,B=0,W>0,C>0`. The explicit
construction and positive center-anchored survivor are recorded in
`5-failed/theta-two-node-source-only-axis-orientation.md`. These coefficients
are not claimed to satisfy `Mc=h`; the actual barriers above remain open.

Thus repeating source convexity arguments cannot settle the remaining
comparison. Retain both projection equations in the next proof attempt.

## Actual signed-energy obstruction and next producer

RN-P-7g now formalizes `cᵀMc=f(0)²/s(0)+∫w f²` and
`α-s(0)=-(s(0)/α)∫wG²`, with exact inverse-Gram coefficients and justified
integrals. RN-P-7h proves `α(0,z)>s(0,z,0)` for every z>0. The negative
signed energy is therefore present in actual representers, not merely
arbitrary coefficients. An independent source-zero packet has positive
signed energy `det(M)α`. The compensated first-axis barrier is still open.

RN-P-7i is closed: the actual sixth logarithmic center jet is positive,
and the proposed four-point inequality has a strict reverse near the
equispaced center. Its radial producer is negative near zero and positive
eventually. See `5-failed/theta-radial-four-point-projection.md` and its
formalized sign-change survivor.

RN-P-7k bypasses coefficient positivity. The exact center confluent entry
is `β=∫(t p'-p)k²>0`. Actual determinant and representer limits give
`A_z(y)→k(y)-k(0)H(0,y)/H(0,0)>0` for every fixed y>0 as z→0⁺.
Both new Lean leaves passed their targeted build, final direct-file audits
and standard-axiom checks; the card is now
`3-formalized/theta/rn-confluent-center-source-residual.md`.
This supplies a genuine actual-source port region. RN-P-7l retains the
coordinate residual's remaining integral sign; the global compensated
barriers and arbitrary-rank continuation are still open.
