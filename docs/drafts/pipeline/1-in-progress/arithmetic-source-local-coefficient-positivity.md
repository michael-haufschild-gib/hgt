# Arithmetic source positivity for the exact local Xi divisor

- **ID:** arithmetic-source-local-coefficient-positivity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Arithmetic Local Divisor Geometry; Astra §§8.1, 9.4
- **Statement:** Starting from the theta/Euler definition of Xi, prove every coefficient of its unnormalized radius-one local divisor polynomial nonnegative, at every real center.

## Exact endpoint

Let `H(t)={q : |z_q-t|≤1}` count every spectral zero copy, including central
copies, and let `D_t(Y)=∏_(q∈H(t))(Y+(z_q-t)²)` with conjugates grouped over
the reals. Prove `[Y^k]D_t≥0` for all `t∈ℝ` and `k∈ℕ`. Existing source
identification and the exact positive complementary tail make this equivalent
to RH. This is the target conclusion, never an assumed input.

The weaker heat endpoint must retain all orders up to the actual degree and
the full height range: a fixed radius in `[1/2,1]`, every `|t|≥73/5`, and
some `0≤λ≤δ₀²/(320 log(180|t|))` with coefficient-positive retained head
after heat `λ/2`. Merely eventual full-slice positivity does not supply it.

## Internal frontier

- Exact unnormalized source, Taylor and signed transition identities:
  `ArithmeticLocalDivisorGeometry/SourceLocalFactors.lean`.
- Exact copy degree, evenness, real-axis nonnegativity and sharp root
  obstruction: `ArithmeticLocalDivisorGeometry/SourceDivisorGeometry.lean`.
- All-height head positivity iff RH:
  `RHTower/XiSliceGaussianFiniteHeadPositivity.lean`.
- First normalized head coefficient equals a compensated Prime–Cesàro
  expression, retaining the finite-head twist and infinite compensated tail:
  `RHTower/XiWardGlobalCapAndFiniteHeadArithmetic.lean`.
- Full heated-slice positivity at `(17/25)/log|t|`, eventually in height:
  `RHTower/XiSliceHeatRateInteriorLindelof.lean`. This is not a retained-head
  sign theorem, and a positive complementary tail cannot be canceled.

## Competing mechanisms under audit

1. **Source determinant:** signed Newton combinations equal exterior minors
   of a source-defined positive operator. Both the exact coefficient identity
   and the operator sign must be proved; root reality cannot enter its domain.
2. **Complete signed source estimate:** retain the prime, Gamma, polar and
   compensated-tail terms and show that their sum has the required sign.
   Separate positive diagonal or moment estimates do not suffice.
3. **Threshold rigidity:** use the actual analytic source to exclude first
   positive-heat contact only at higher orders. Generic heat and norm-square
   properties do not exclude it, by the formalized masked-pair and Hermite
   extremizers.

**[OPEN CORE]** No independently proved signed arithmetic inequality or
positive determinant identity currently gives the all-height, all-order sign.
The next research must attack this input, rather than restate the receiver.

## Primary-literature audit

- [Csordas, *Fourier transforms of positive definite kernels and the Riemann
  xi-function*, v2](https://arxiv.org/html/1309.0055v2), Theorem 3.7:
  positivity of every associated kernel is exactly the generalized Laguerre
  criterion. Strict source log-concavity establishes admissibility of those
  kernels, not positive definiteness. Example 3.12 explicitly separates the
  first two orders. Thus an appeal to this kernel representation alone is
  **REDISCOVERED**, not an arithmetic positivity proof.
- [Sra, *On some positivity properties of the Riemann Xi function*, v1,
  20 October 2026](https://suvrit.github.io/papers/riem-xi/): the stated global
  finite-order PF result and local fixed-order results do not give arbitrary
  order at every center. Its all-order Laguerre conclusion on a bounded
  interval uses zero verification through a larger height. No such verification
  is silently extended to unbounded height here.
- [*Generalized Laguerre positivity at growing orders*, v4,
  24 October 2026](https://rstation.ai/problems/riemann_hypothesis/papers/41):
  the preprint states high-order positivity, exceptional-set bounds and
  filtered mean positivity. It expressly leaves small fixed orders and
  exceptional zero ordinates unresolved. These claims are not imported as
  Lean inputs or upgraded to local-head positivity.
- [Liu, *Improved zero-free half-planes for the quasi-Riemann hypothesis*,
  v2](https://arxiv.org/html/2610.12234): the stated bound is approximately
  `0.8749570194`, with an optimality result for its specified exponent
  comparison system. Its iteration has a fixed point above `1/2`; repeating
  that iteration does not establish RH. The cubic-theta method supplies a
  different arithmetic exclusion mechanism, not the missing coefficient
  identity. No external formalization has been imported or independently
  checked in this investigation.

## Direct source-kernel attack

The existing `XiSliceHeatTransferPositivity` and
`XiSliceHeatHermiteRepresentation` identities give, with the actual even
theta kernel `Φ` and `m≥0`,

`(2m)! T_(2m)(λ,0,t) = ∫∫ Φ(u)Φ(v) exp(it(u+v))
  (u−v)^(2m) exp(λ(u−v)²/2) du dv`.

Changing `v` to `−v` turns this into the quadratic form on
`g_t(u)=Φ(u)exp(itu)` with real symmetric kernel

`K_(m,λ)(u,v)=(u+v)^(2m) exp(λ(u+v)²/2)`.

This does **not** give a positive Gram kernel. For `m≥1` and `a≠0`, its
principal matrix at `0,a` has determinant

`K(0,0)K(a,a)−K(0,a)² = −a^(4m) exp(λa²)<0`.

Multiplying by the positive theta weights leaves that determinant negative.
Thus positivity cannot follow for arbitrary test amplitudes from this literal
kernel. This rejects the proposed universal Gram inference; it does not
produce a negative value on the particular arithmetic orbit `g_t`, and does
not retire a different, source-specific operator construction. The surviving
arithmetic question is precisely how the theta/Euler source restricts that
orbit sufficiently to prevent the negative directions from being seen.

An elementary check of Csordas's example makes the order gap explicit. Its
Fourier transform is a positive constant times
`F(t)=exp(−t²/4)(t⁴−16t²+260)`. At `t²=8`, setting `Y=x²` gives

`F(t+ix)F(t−ix)=exp(−4) exp(Y/2)
  ((196−32Y+Y²)²+128Y³)`.

The constant, `Y`, and `Y²` coefficients before the common positive factor
are respectively `38416`, `6664`, and `−54`. The last identity uses
`1416−12544/2+38416/8=−54`. This is an exact algebraic illustration of the
published counterexample, not numerical evidence about Xi and not a new
research theorem. It prevents substituting low-order source inequalities
for the missing complete sign.

## Exact signed inequality still needed

Away from central zeros, write `A_k(t)=[x^(2k)]S(t,x)/Xi(t)²` and let
`B_k(t)` be the exact complementary-tail coefficients, with `B_0=1`.
For the normalized radius-one head coefficients `d_k`, exact factorization
gives

`d_0=1`,
`d_k=A_k−Σ_(j=1)^k B_j d_(k−j)`.

In particular, the first two required inequalities are

`A_1≥B_1`,
`A_2−B_1 A_1+B_1²−B_2≥0`.

Full-slice coefficient positivity `A_k≥0` and tail positivity `B_k≥0`
do not prove these subtractions nonnegative. The existing compensated
Prime–Cesàro identity supplies the exact first signed expression, retaining
the finite-head twist, remainder and compensated infinite tail. None of the
inspected estimates bounds that complete expression with the required sign.
At central zeros the unnormalized source polynomial must be used; division
by `Xi(t)²` is invalid. Every order through the actual degree remains required.

## Assessment and continuation

The investigation has not proved arithmetic source positivity or moved its
sign frontier. The literal Gram approach is indefinite; its associated-kernel
reformulation is classical. No new mathematical claim is ready for Lean.
The existing formalized polynomial and source bridges remain valid.

Next proof attempt must estimate the complete signed Prime–Cesàro/Newton
combination, or construct a different source-specific positive identity.
Further generic kernel positivity, fixed-order asymptotics, tail cancellation
or optimizations within the audited quasi-RH exponent system cannot fill the
identified gap. The main conjecture remains in progress; no route is retired
and no assumption is promoted to a proved theorem.

## Research gates

- [x] Inspect corpus frontier before mathlib.
- [x] Audit current primary literature and adjacent equivalent statements.
- [ ] Select an exact source conjecture and attack falsity, circularity and duplication.
- [ ] Complete its dependency-closed paper proof.
- [ ] Formalize only the proved statement, with individual `lake --old env lean`
  checks and standard-only transitive axiom audits.

No Python jobs, numerical experiments, extra analytic premises, placeholders or
proof-limit changes. Preserve the completed formalization in the parent card.
