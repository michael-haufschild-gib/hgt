# Joint infinite coprime trace interpolation

Status: dependency-closed paper proof; Lean verification pending. One package,
not yet counted. Spacings m=d+2 and n=e+2 are arbitrary integers at least two.

## Concrete data and construction

Write H_a=1_(a−1,a]−1_(a,a+1], E_d a=Σ_j a_j H_(m(j+1)),
P=P_d, Q=P_e, R=P_lcm. Existing infinite synthesis proves convergence in
physical L² and all integer primitive traces; each family has energy 2‖a‖².
Define the actual closed subspace

    D={ (a,b)∈ℓ²×ℓ² : R(E_e b)=0 }.

It is a continuous linear map's kernel. Self-adjointness of R and the established
formula R H_(n(j+1))=1_(m|n(j+1)) H_(n(j+1)) imply

    coefficient_e(R E_e b)_j = 1_(m|n(j+1)) b_j.

Thus D means exactly that second-family values vanish at shared nodes. Every
ℓ² datum on the union is encoded once: assign shared nodes to a, the others to b.
Arbitrary pair data canonically produce D by replacing b by
b−coefficient_e(R E_e b). The residual is in the e-family, and R kills it by
idempotence. There is no assumed convergence or analytic admission condition.

Set E(a,b)=E_d a+E_e b and M(a,b)=‖a‖²+‖b‖². Integer primitive traces equal
a_(k/m−1) when k>0 and m|k, b_(k/n−1) when k>0, n|k but m∤k, and zero
otherwise. Consequently logPrimitive E(log k) has those same values for k>0.
M is the sum of squares of union values, with common nodes counted once.
The product's ambient Banach norm is max(‖a‖,‖b‖); M is stated separately.

## Exact infinite adjacent energy

Put B(k)=primitive(E_e b)(k), including B(0)=0. Its value at every first-family
center is zero. The identity ⟨H_r,E_e b⟩=2B(r)−B(r−1)−B(r+1) therefore gives

    ‖E(a,b)‖² = 2M(a,b)
      −2 Σ_j a_j [B(m(j+1)−1)+B(m(j+1)+1)].

The scalar summand series is absolutely summable: synthesis of a converges
unconditionally in L², and the continuous inner-product functional carries
it to a summable real series. The displayed sum enumerates every adjacent
union-node pair exactly once. A shared node has no adjacent union node: either
spacing would then divide consecutive integers. Within either individual grid
adjacency is impossible. Hence this is precisely
2Σ_(r∈U)v_r²−2Σ_(r,r+1∈U)v_r v_(r+1), without a double-counted edge or node.

## Sharp arithmetic stability

Let T=PQ−R and c=0 if gcd(m,n)≥2, c=1/2 if gcd(m,n)=1 and min(m,n)=2,
and c=1/4 otherwise. The already proved operator identities give ‖T‖=√c.
For x=E_d a and y=E_e b, Px=x, Qy=y, Ry=0. Therefore

    |⟨x,y⟩|=|⟨x,Ty⟩|≤√c ‖x‖‖y‖≤√c M(a,b).

Thus (2−2√c)M≤‖E(a,b)‖²≤(2+2√c)M. These are exactly (2,2), (1,3),
or (2−√2,2+√2). The lower factor is at least 2−√2>1/2, so E is injective
and ‖z‖≤2‖Ez‖. On the complete closed space D this gives an antilipschitz
continuous linear map with closed range. Every sum E_d a+E_e b belongs to
this range: transfer R E_e b into the first family, subtract it from the
second. Hence the algebraic sum V_m+V_n is already closed.

Sharpness is attained, not merely approached. For c=0 any nonzero first-family
tent works. For c>0, set A=T* T. The previous polynomial laws imply A²=cA;
A≠0. Choose z with Az≠0 and set y=Az. Then Qy=y, Ry=0, Ay=cy, and
‖Ty‖²=c‖y‖². Put x=Ty/√c. It lies in V_m, has ‖x‖=‖y‖, and
⟨x,y⟩=√c‖y‖² because Py=Ty and P is an orthogonal projection.
Convert x and y to their actual synthesis coefficients. The data (x,y)
attain the upper constant; (−x,y) attain the lower constant. Their mass is
positive. This also handles either orientation of the spacing-two exception.

## Exact competitor defect

For any physical L² q and z=(a,b)∈D, put r=q−Ez. Polarization and convergent
synthesis yield the unconditional identity

    ‖q‖² = ‖Ez‖²+‖r‖²
      +2Σ_j a_j curvature_d(r)_j +2Σ_j b_j curvature_e(r)_j.

Both scalar series are summable by the same continuous-functional argument.
If q has the prescribed trace at every nonnegative integer, all integer traces
of r vanish, hence both curvature series vanish. Exact excess energy is then
‖r‖², and equality uniquely forces q=Ez. This is minimum energy with all
off-union integer traces fixed to zero; prescribing only union traces is a
different variational problem. The unconditional identity keeps trace mismatch
visible rather than using blindness as an admission premise.

## Context and scope

Finite hat interpolation is classical; see Driscoll–Braun,
[Piecewise linear interpolation](https://fncbook.com/pwlin/).
Friedrichs-angle control is also classical; the contribution here is the actual
infinite arithmetic trace domain, exact adjacent energy, sharp arithmetic
constants, closed sum and precise competitor defect for the existing continuum
coprime shear objects. No external novelty claim for the parent methods.
Physical primitives become logarithmic primitives by t=exp x; existing rough
transport identifies physical energy with weighted logarithmic derivative energy.
No unweighted logarithmic H¹ or full affine unitary representation is claimed.

Corpus check: initial long AND query returned four candidate and four source
arguments unrelated to this construction (partial=false, errors=[]); broad query
was interrupted and its handle disappeared, leaving empty output. Focused
replacement query `coprime extension projection` completed: all 16 candidate
lemmas and 17 source arguments inspected, partial=false, errors=[]; it finds
individual-grid synthesis, projection and finite interpolation defects, no joint
domain. Semantic coverage is unmeasured and background refresh incomplete.
No inference of global novelty from incomplete semantic coverage.
