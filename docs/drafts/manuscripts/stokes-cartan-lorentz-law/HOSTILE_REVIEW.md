# Hostile referee report

Manuscript: *The Euler--capacity law for wild character varieties*

Audit date: 2026-08-03

Target: renowned broad mathematics journal with geometry/representation-theory readership
(Compositio Mathematica / Advances in Mathematics / Duke Mathematical Journal band). This is an
internal adversarial report, not external peer review or a guarantee of acceptance.

## Recommendation

**Pass: suitable for submission in target band.** Central theorem is now global, memorable, and
strictly stronger than manuscript's former genus-zero matrix theorem:

`Q_(X,D) = sum_a P_a(z_a) + (chi(X) - sum_a delta_a) M^2`,

with every `P_a` positive definite and `delta_a = 2 - Omega_a` determined variationally by local
Stokes data. Prior genus-zero factorization, corona resistance, Rees stability, dimension
conservation, Fourier rank constraints, and graph spectral bound are genuine corollaries.

I would not market current paper as Annals/Inventiones level: categorical microlocal realization of
positive conormal terms remains open. But paper clears a strong general-journal threshold because it
proves an arbitrary-genus index theorem, resolves all inertia, gives a new restriction on
nonabelian-Hodge/Kac--Moody diagrams, and has complete finite algebra with formal verification.

## Attacks

### 1. “Global law is an arithmetic error in quasi-Hamiltonian dimensions.”

For `G=GL_M`, local Stokes space has dimension `M^2+h_a+s_a`. Global framed space has

`(2g-2)M^2 + sum_a(M^2+h_a+s_a)`.

Reduction adds `sum k_a`, subtracts `2 sum h_a`, and restores `2 dim Z(GL_M)=2`. Hence

`dim M_(X,D)=2+(2g-2+m)M^2+sum_a(s_a+k_a-h_a)`.

Thus `Q_(X,D)=2-dim M_(X,D)` differs from `sum Q_a`, with
`Q_a=M^2+h_a-s_a-k_a`, by exactly `2(1-g-m)M^2`. Signs and center correction are correct.
Objection fails.

### 2. “Boalch 2014 is unramified; manuscript silently applies it to ramified poles.”

This was a real first-draft defect. Revision defines `s_a` intrinsically by local Stokes-space
dimension and cites Boalch--Yamakawa's twisted quasi-Hamiltonian construction for ramified formal
types. Root-sum formula is stated only for unramified Cartan normal form. Objection closed.

### 3. “Local atom positivity is assumed, not proved.”

Sections 2--6 prove it. Complementary Stokes contacts have one simultaneous rooted realization;
entrywise conversion gives

`C = I + sum_e ell_e u_e u_e^T - lambda rr^T`.

Type-A path completion replaces unit terminal weights by positive `1/(l_i+1)` and adds strictly
positive fluctuation squares. Thus every marked one-puncture atom is positive on rank kernel and
has exact capacity completion. Objection fails within stated type-A scope.

### 4. “Quadratic refinement is merely a scalar rigidity formula rewritten.”

No. Scalar rigidity evaluates `Q` at one integral marking. Manuscript identifies entire real
polarization on fixed marked lattice and proves strict positivity on every nonzero rank-zero
direction. Two quadratic forms can agree at one vector and have different inertia; Hiroe's scalar
Euler-characteristic theorem cannot imply the result. The new law determines negative index,
nullity, affine ray, constrained minimum, and all mixed bilinear terms. Objection fails.

### 5. “Calling this a Hodge index theorem is branding without Hodge theory.”

Correct criticism of an intermediate draft. Final title and theorem use “Euler--capacity” and
“one-port index”; no Hodge structure is claimed. Objection removed rather than argued away.

### 6. “Any positive covector would give the same rank-port statement.”

False, and manuscript includes direct falsifier. For realized twisted triangle,

`e_1^T C^{-1}e_1=5/258>0`,

while physical rank covectors `(3,2,3)` and `(2,1,4)` give `-245/86` and `-104/129`. Geometric rank
compatibility is load-bearing. Every admissible reading is handled by applying local law in that
reading, not by coefficient positivity. Objection fails.

### 7. “Multiple punctures introduce multiple negative ports.”

They would on unrestricted direct sum. Global deformation lattice is rank fibre product, so all
local rank values equal one scalar `M`. Centering each local atom leaves `sum P_a(z_a)` plus one
coefficient times `M^2`. This is exact reason nonpositive inertia remains one-dimensional.
Objection fails.

### 8. “Higher genus can add independent handle defects.”

Handle contribution is `-2gM^2`; it changes same common-rank coefficient and no centered variable.
Consequently each handle sends `Omega` to `Omega-2`, affine genus is unique if it exists, and
connected sum obeys `Omega_(X#Y)=Omega_X+Omega_Y-2`. Objection fails.

### 9. “Capacity depends on artificial root height.”

Local Sherman--Morrison law gives `c_t=c/(1+tc)`, hence
`c_t^{-1}-(lambda+t)=c^{-1}-lambda`. Electrical formulation says same root segment is added to
effective resistance and defect. Global coefficient is also characterized without root choice as
minimum of `Q_(X,D)` at unit common rank. Objection fails.

### 10. “Microlocal/Rees/vanishing-cycle vocabulary is decorative.”

Principal conormal and Rees claims are exact finite statements: `d nu_e=u_e`, Hessian is
`D+sum ell_e dnu_e tensor dnu_e`, and nonnegative Rees scaling preserves one defect. Corona pruning
is exact Schur/parallel elimination. Manuscript explicitly refuses categorical identification with
characteristic or vanishing cycles. Terminology is bounded; categorical lift remains open.

### 11. “Formalization proves a toy core but not physical fibre product or legs.”

This exposed another intermediate gap. Final Lean development defines dependent local dimensions,
actual compatible-rank submodule, global quadratic form, exact capacity centering, and `sigNeg`.
Separate full-marking module constructs dependent type-A increment spaces and proves fused
arbitrary-genus negative index at most one. Geometric realization and published analytic dimension
formula remain explicit interfaces rather than fake formalizations. Objection closed.

### 12. “Result remains too elementary for broad journal.”

Linear algebra after correct decomposition is elementary. Geometric content is discovering and
proving decomposition for full ramified type-A Stokes class and showing quasi-Hamiltonian topology
couples only through physical rank. Consequences address active classification question: every
genus-zero nonabelian Hodge graph has `lambda_2<=2`; higher-signature symmetric Kac--Moody diagrams
are excluded, while realized twisted triangle shows sharpness. Arbitrary-genus Euler--capacity law
substantially broadens reach. This meets target band, though editors may still prefer categorical
lift.

## Proof audit

| Result | Hostile check | Outcome |
|---|---|---|
| Contact dendrogram | Threshold relation orientation and diagonal strictness | Correct |
| Geometric input | Pairwise-vs-simultaneous tree; weak-representation overreach | Common tree and diagram-only transport stated precisely |
| Local factorization | Diagonal loops, off-diagonal contacts, ramification signs | Entrywise identity correct |
| Capacity normal form | Coefficient of fixed rank | `M^2/c-lambda M^2=Omega M^2` |
| Root invariance | Sherman--Morrison denominator and determinant | Correct, denominator positive |
| Corona recursion | Series/parallel equality, not heuristic | Exact constrained minimum |
| Full legs | Core square double counting and Schur terminal weight | Correct `1/(l_i+1)` |
| Rees | Zero edge parameters could destroy strict positivity | Positive terminal diagonal remains |
| Fusion identity | Genus, puncture, center coefficients | Correct as in Attack 1 |
| Euler--capacity theorem | Fibre-product dimension and uniqueness | Orthogonal positive space plus one scalar line |
| Physical ranks | Arbitrary-covector counterexample | Included; claim limited to geometric readings |
| Variational law | Negative phase minimum well-defined at fixed rank | Constraint removes scale; unique positive-part minimizer |
| Graph spectrum | Eigenvalue ordering and affine multiplicity | `Spec(2I-B)=2-Spec(B)` gives stated result |

## Novelty audit

Primary sources checked: Biquard--Boalch 2004; Boalch 2014; Boalch--Yamakawa 2015 and 2020;
Douçot 2021, 2025, and 2026; Boalch--Douçot--Rembado 2025; Hiroe 2017 and 2019; closest
ultrametric/inverse-M-matrix literature through Nabben 2026. Exact and near-exact searches found no
Euler--capacity, rank-fibre-product inertia, physical-rank timelike, or wild-character
second-eigenvalue theorem. Negative search is not absolute priority proof; expert circulation is
still required.

Novelty does **not** consist of rank-one perturbation, Schur complement, electrical reduction,
quasi-Hamiltonian dimension formula, or scalar rigidity/Euler identity separately. It is their new
geometric synthesis forced by Stokes normalization, plus resulting arbitrary-genus polarization
and classification consequences.

## Lean audit

New universal modules:

- `StokesEulerFusionCapacity.lean`
- `StokesEulerFusionTypeALegs.lean`

Checks:

- `lake env lean` passed for both modules;
- targeted `lake build` passed for both modules;
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration occurs in either;
- capstones report only `propext`, `Classical.choice`, and `Quot.sound` under `#print axioms`;
- both modules are wired into `GaloisForLFunctions/HTGeometry.lean`;
- no Lean/lake process owned by this task remains.

Repository-wide lint remains red solely on unrelated shared-worktree unreachable modules in
`RHTower` and three unrelated `HTGeometry` files (`ClockSolutionSecondTransverse`,
`NevanlinnaCoeffFun`, `TwoRecordResolvedConnection`). New Stokes modules do not appear in errors.

## PDF audit

- 17 A4 pages, visually inspected;
- no TeX errors, undefined references, overfull/underfull boxes, clipped displays, or broken glyphs;
- title avoids unsupported Hodge-theoretic branding;
- universal theorem appears in abstract, introduction, main theorem, conclusion;
- final PDF SHA-256:
  `4c5345192072cdad9d75a158737993c36c56bd7f00a0e371d1e1c905e278caef`.

## Final judgment

**Confirmed at internal hostile-review level: complete and strong enough for submission to a
renowned broad mathematics journal in stated target band.** Remaining risks are normal external
ones: priority under alternate terminology, editor breadth judgment, and demand for categorical
microlocal lift. They are not hidden proof gaps in theorem as stated.
