# Two quartets preserve the endpoint jet

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacles:** B13, B112; arithmetic detection of finite exceptional divisors.
- **Statement:** Four distinct actual critical-line donor pairs admit a monic symmetric rational relocation into two quartets on `Re s=1/4,3/4`, preserving `R(1)=1` and `R'(1)=0`. Cancelling one zero copy at each donor gives an entire finite surgery on `xi`, retaining reflection, reality, and both first endpoint jets.
- **Contribution count:** One (#13), including scalar interpolation, the actual donor construction, and entire cancellation. Two quartets are sufficient and minimal within the monic quartet-relocation class.
- **Novelty boundary:** `EndpointNormalizationForcesANegativeQuartetTrace` excludes this for one quartet. Corpus searches found no two-quartet endpoint-jet construction. Mean-spectrum preservation and failure of exact Dirichlet realization are existing results, not additional contributions.

## Proof

Write `a_j=gamma_j^2+1/4`, `P=product a_j`, and `S=sum 1/a_j`, with four donor heights above one. Fix transverse depth `1/4`. Parameterize each target quartet by `u=eta^2+5/16`; its endpoint value is `A(u)=u^2-1/16` and logarithmic derivative is `d(u)=2(u-1/8)/A(u)`.

For `5/16 <= v <= sqrt(1/16+sqrt P)`, put
`u(v)=sqrt(1/16+P/A(v))`. Then `A(u(v))A(v)=P`.
Put `r=sqrt P`, `w=sqrt r`, and `b=sqrt(r+1/16)`. Since every `a_j>1`, both `r,w>1`. On `[5/16,b]`, `A(v)>=9/256>0`, `A(v)<=r`, and `u(v)>=b`. Also `u(b)=b` and `A(u(v))A(v)=P`.

At the left endpoint `d(v)=32/3>S`, since `S<4` and `d(u(v))>0`. At the right endpoint, `b<w+1/8`: squaring reduces this to `w/4>3/64`. Thus
`d(u(b))+d(b)=4(b-1/8)/r<4/w<=S`, where the last inequality is AM-GM on the four reciprocals `1/a_j`. Continuity gives `v` strictly between the endpoints with `d(u(v))+d(v)=S`. Moreover `u(v)>=b>v>5/16`, so the ordinates `sqrt(u-5/16)` and `sqrt(v-5/16)` are positive and distinct.

For `eta=sqrt(u-5/16)`, the quartet numerator at `rho=3/4+i eta` equals
`Q_u(s)=((s-1/2)^2+u-3/8)^2+(u-5/16)/4`.
It has `Q_u(1)=A(u)` and `Q_u'(1)=2(u-1/8)`. The product of the two quartet numerators consequently has the same value and logarithmic derivative at one as the four donor-pair denominator. Their quotient has value one and derivative zero. Each quartet factor is invariant under `s -> 1-s` and conjugation. Reflection therefore gives the same endpoint value and zero derivative at zero. Its eight numerator zeros lie on `Re s=1/4,3/4` and are distinct; the two off-line quartets cannot cancel critical-line denominator factors. Monicity gives limit one at vertical infinity.

The corpus's unbounded critical-line zero theorem supplies four strictly increasing donor heights above one, without RH or simplicity assumptions. The one-quartet negative-derivative theorem excludes a nontrivial one-quartet construction with the same endpoint jet. Thus two quartets are sufficient and minimal within this class.

The multiplier also defines an entire finite surgery on `xi`. Let `D` be the product of its eight distinct donor factors. Repeated divided differences at the donor zeros give an entire `G` with `xi=DG`; each division leaves all remaining distinct donor zeros intact. Put `F=G Q_u Q_v`. Off the critical line, `F=xi R`. The identity theorem transfers reflection and reality from this equality to all of `C`. Near zero and one the denominator is nonzero, so the multiplier's preserved jet gives `F=xi` and `F'=xi'` at both endpoints. Both off-line quartets are zeros of `F`. No assumption about simplicity of any donor zero is needed.

## Lean certificate

Paths are relative to `formal/GaloisForLFunctions/ArithmeticPositiveDuality/`.

| Module | Capstone |
|---|---|
| `TwoQuartetEndpointInterpolation.lean` | `exists_two_quartet_endpoint_parameters` |
| `TwoQuartetsPreserveTheEndpointJet.lean` | `exists_actual_two_quartet_endpoint_jet` |
| `TwoQuartetsPreserveTheEndpointJet.lean` | `tendsto_twoQuartetFactor_vertical` |
| `TwoQuartetSurgeryPreservesXiEndpointJets.lean` | `exists_entire_xi_surgery_preserving_endpoint_jets` |

All three modules pass direct `lake --old env lean` audits without warnings.
Capstones have only `propext`, `Classical.choice`, and `Quot.sound` as
transitive axioms. Modules are umbrella-wired. The single-quartet obstruction
is `quartet_deriv_one_neg_of_endpoint` in
`EndpointNormalizationForcesANegativeQuartetTrace.lean`.

The result identifies a precise limitation of endpoint normalization and
first derivatives as zero-divisor detectors. RH and the original finite-defect
obstacles remain open.
