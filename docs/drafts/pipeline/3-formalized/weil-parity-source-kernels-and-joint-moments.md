# Exact parity source kernels and independent constrained source moments

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Modules:** `RHTower.CCMRestrictedWeilPolarParitySourceProfile` (5 public theorems, 3 definitions); `RHTower.CCMRestrictedWeilPolarParitySourceCoupling` (10 public theorems, 2 definitions). Both wired into `RHTower.lean`.
- **Predecessor:** [Ground source moment and nonvanishing](weil-ground-source-moment-and-nonvanishing.md).
- **Active continuation:** [Ground-specific signed source control](../1-in-progress/weil-gamma-pole-boundary-action.md).

## Full proof chain and scope
Exact prime–Gamma action → control of the selected constrained ground's forcing → exclusion of a zero ground → all-aperture positive floors → weighted pole exclusion → RH. The present results identify both actual parity source kernels, prove source nonvanishing separately in each completed constrained parity sector, and show the original and reflected source moments are jointly surjective. They do not determine the moment of a selected ground or exclude its forced zero equation.

## Conjecture → proof / pivot loop
1. **Question:** does nonvanishing on the full constrained space persist in each parity separately? Nonvanishing on their sum alone gives no answer.
2. **Candidate:** both channels share a singular boundary term with coefficient `exp(x/2)+r exp(-x/2)`, `r=±1`, and have bounded remaining terms on every fixed aperture. **Proved:** the exact bounded boundary asymmetry and literal arithmetic-error bounds give the full decomposition.
3. **Endpoint conjecture:** the odd channel might cancel the singularity. **False:** its right-end coefficient is `exp(a/2)-exp(-a/2)>0`; the even coefficient is positive as well. Both profiles tend to positive infinity there.
4. **Physical identification:** the profiles must represent actual reflected L² defects and continuous form-domain functionals. **Proved:** measure-preserving reflection transports the existing almost-everywhere coefficient formula, and reflection symmetry transports the complete inner product.
5. **Positive survivor:** each constrained parity sector realizes every complex source moment; combining even and odd witnesses realizes an arbitrary pair of original and reflected moments. **Proved.** Neither parity decouples automatically.
6. **Remaining comparison:** constrain those moments using the selected ground equation and its normalization. Their freedom on arbitrary constrained vectors supplies no ground sign.

## Dependency-closed paper proof
Fix `a>0`, let `R=a-x`, `L=a+x`, and retain the exact arithmetic error

`A_a(x)=E_psi(exp(a-x))+E_M(a+x)`.

The actual positive-pole source profile is `K_a(x)=exp(x/2)[B(R,L)-A_a(x)]`. On the open aperture, monotonicity and nonnegativity of `psi`, together with the existing elementary Mertens bound, imply

`|A_a(x)|≤C_a`,

`C_a=psi(exp(2a))+exp(2a)+log 4+5`.

Every prime power is retained. Let

`Delta_a(x)=B(R,L)-B(L,R)`.

The preceding exact boundary decomposition proves `|Delta_a(x)|<log 2`. For either parity `r=±1`, define

`K_(a,r)(x)=K_a(x)+r K_a(-x)`,

`T_(a,r)(x)=exp(x/2)A_a(x)+r exp(-x/2)[A_a(-x)+Delta_a(x)]`.

Algebra, before any estimate, gives the exact real-valued identity

`K_(a,r)(x)=[exp(x/2)+r exp(-x/2)]B(R,L)-T_(a,r)(x)`.

Since both exponentials are at most `exp(a/2)` on the aperture and `|r|=1`,

`|T_(a,r)(x)|≤exp(a/2)[2C_a+log 2]`.

This is a finite bound at each fixed aperture, used to isolate the endpoint singularity. It is not an all-aperture Weil positivity estimate.

The common boundary factor tends to positive infinity as `x→a` from below. Its channel coefficient tends to `exp(a/2)+r exp(-a/2)>0` for both parities. Subtracting the bounded remainder therefore proves

`Re K_(a,r)(x)→+infinity`.

### Actual physical source and pure-parity pairing
Let `d_a` be the actual aperture L² defect whose coefficient is the cutoff of `K_a`, let `R_a` be physical reflection, and let `J_a` be the complete form-domain embedding. Define

`d_(a,r)=d_a+r R_a d_a`,

`G_(a,r)(u)=F_a(u)+r F_a(R u)`,

where `F_a(u)=<d_a,J_a u>`. The existing weighted form reflection satisfies `J_a R=R_a J_a`, and physical reflection is self-adjoint. Hence

`G_(a,r)(u)=<d_(a,r),J_a u>`.

Measure-preserving reflection transports the almost-everywhere coefficient formula for `d_a`. The actual `d_(a,r)` therefore has coefficient `1_[-a,a]K_(a,r)`, giving the complete-domain integral identity

`G_(a,r)(u)=integral_[-a,a] K_(a,r)(x)(J_a u)(x) dx`.

Both factors are actual L² representatives, so the product is integrable. If `R u=r u`, complex linearity and `r²=1` give `G_(a,r)(u)=2F_a(u)`. Thus the forcing numerator of a pure-parity state is exactly

`F_a(u)=(1/2) integral_[-a,a] K_(a,r)(x)(J_a u)(x) dx`.

No scalar reflection factor or normalization is omitted.

### Separate nonvanishing and joint surjectivity
Endpoint divergence rules out an almost-everywhere finite upper bound for `Re K_(a,r)` on the open aperture: every sufficiently small endpoint neighborhood contains a positive-measure open interval where the profile exceeds the proposed bound. Every two-pole coefficient is continuous and bounded on the compact aperture. Consequently `d_(a,r)` cannot be any two-pole vector.

If `G_(a,r)` vanished on the completed constrained sector, exact continuous-annihilator classification would represent it by a two-pole vector. Density of `J_a` would identify that vector with `d_(a,r)`, a contradiction. Choose constrained `v` with `G_(a,r)(v)≠0`. Then

`u=v+r R v`

is constrained, satisfies `R u=r u`, and has `F_a(u)=G_(a,r)(v)≠0`. Scaling this vector realizes any prescribed complex value of `F_a` within that same parity sector.

Finally, for an arbitrary pair `(z_1,z_2)`, choose an even constrained vector `e` with source moment `(z_1+z_2)/2` and an odd constrained vector `o` with moment `(z_1-z_2)/2`. Their sum satisfies

`F_a(e+o)=z_1`, `F_a(R(e+o))=z_2`.

Therefore the original and reflected source moments are jointly surjective on the actual completed constrained space. This is a statement about admissible source vectors; a ground's extra variational equation remains essential.

## Verification
- Scratch `lake env lean /tmp/hgt-parity-source.91OGyY/Profile.lean` and `Physical.lean`: PASS.
- Named final leaf builds of `GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarParitySourceProfile` and `GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarParitySourceCoupling`: PASS (6.8 and 10 seconds). No full or umbrella build.
- No numerical experiment, computational oracle, added axiom, or RH premise supplies these results.
- Scratch `Audit.lean`: all 15 public theorems have exactly `[propext, Classical.choice, Quot.sound]`; actual mathlib `RiemannHypothesis` printed and remains unproved.
- Final `python3 scripts/formal_tools.py lint`: PASS (`formal lint passed`); existing size warnings remain. Logs: `/tmp/hgt-parity-source.91OGyY/Lint.txt` and `.err`.
- `git diff --check`: PASS. Corpus research index refreshed; all owned Lean/build processes terminal.
