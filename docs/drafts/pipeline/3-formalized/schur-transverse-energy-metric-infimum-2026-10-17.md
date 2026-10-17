# Sharp metric-conditioning frontier of actual Xi Jordan chains

- **ID:** schur-transverse-energy-metric-infimum-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM with a dependency-closed paper proof
- **Source:** whole local Lean corpus; contribution 8, counted once
- **Count:** 8/100 verified contributions

For every actual Xi support point rho of multiplicity m, the centered arithmetic
jet operator has minimum quadratic trace-energy defect

`2*m*(Re rho-1/2)^2 + (m-1)/q^2`

under Taylor-frame condition-number budget `q^(m-1)`, for every q>=1.
An explicit positive geometric metric attains the minimum. The statement includes
simple zeros and makes no RH, simplicity, off-line-zero-existence or replacement-
source assumption. The reference Taylor norm is part of the theorem.

The root-free Schur defect is `D(M)=||M||_HS^2-Re Tr(M^2)`. The result combines its
exact decomposition, positive metric conditioning, and the literal arithmetic
jet chains. Frontier map remains read only.

## Closed paper theorem: exact finite-chain conditioning frontier

This contribution is the sharp single-chain law and its literal Xi derivative-jet
realization. The complete classification, minimizing frames, nonattainment
boundary and native coordinate transport count together once.

Let n >= 1, let J be the unit superdiagonal shift on C^(n+1), let alpha be any
complex number, and put A = alpha I + J. Norms below are Euclidean operator
norms, and HS denotes the Hilbert--Schmidt norm. For every q >= 1,

    min { D(P A P^-1) : P invertible, ||P|| ||P^-1|| <= q^n }
      = 2(n+1)(Im alpha)^2 + n/q^2.

The explicit minimizer is P = diag(1,q,...,q^n); its condition number is
exactly q^n and its Gram matrix P*P is positive definite. Thus this is an
attained variational law over all invertible metric frames, not an estimate
for diagonal frames alone. Reparameterizing q = K^(1/n) gives every K >= 1.
The induced Gram matrix has condition number K^2. The scalar n=0 case has
constant energy 2(Im alpha)^2 and needs no conditioning penalty.

### Dependency-closed proof

1. Put N=PJP^-1. It satisfies N^(n+1)=0. Choose a unitary Schur form T of N.
   Its diagonal vanishes: each diagonal entry of T^(n+1) is the corresponding
   diagonal entry of T raised to n+1. Hence T is strictly upper triangular.
2. In a product of n entries of T, a nonzero term requires n strict index
   increases in {0,...,n}. The only possible path is 0,1,...,n. Therefore
   T^n has only its (0,n) entry nonzero, equal to the product of the n adjacent
   entries. Consequently

       ||N^n||^2 = product_i |T(i,i+1)|^2
         <= (sum_i |T(i,i+1)|^2 / n)^n
         <= (||N||_HS^2 / n)^n.

   These steps use unitary invariance of both norms, finite AM--GM, and
   inclusion of the adjacent entries in the full nonnegative HS sum.
3. The inverse similarity identity J^n=P^-1 N^n P and ||J^n||=1 imply
   1 <= kappa(P)||N^n||. If kappa(P)<=q^n, squaring and using step 2 gives
   1 <= q^(2n)(||N||_HS^2/n)^n. Since n>0 and all bases are nonnegative,
   taking ordered n-th powers backwards yields ||N||_HS^2 >= n/q^2.
4. Nilpotence and triangularization give Tr N=Tr N^2=0. Expanding the HS sum
   of alpha I+N eliminates the cross term using Tr N=0. Expanding its squared
   trace and using |alpha|^2-Re(alpha^2)=2(Im alpha)^2 gives

       D(alpha I+N)=2(n+1)(Im alpha)^2+||N||_HS^2.

   Together with step 3 this proves the lower bound for every admissible P.
5. For P=diag(q^i), entrywise multiplication gives PJP^-1=q^-1 J.
   The diagonal norm formula gives ||P||=q^n and ||P^-1||=1. There are exactly
   n nonzero unit entries in J, hence D(PAP^-1) equals the stated lower bound.
   Invertibility of P also proves positive definiteness of P*P. This proves
   membership and leastness, including q=1.
6. For an actual Xi support point rho of multiplicity m, the corpus's centered
   derivative-jet matrix B has diagonal alpha=xiSpectralPointSupport rho and
   subdiagonal k. Let F=diag(k!). Then F^-1 B F has subdiagonal one, because
   k (k-1)! = k!. Index reversal R is unitary and gives

       R F^-1 B F R = xiLocalJordanMatrix rho.

   Thus arbitrary frames Q in the Taylor/reversed coordinates correspond to
   native frames Q R F^-1. Their positive Gram forms are literal positive
   forms on the actual finite jet space. Existing surjectivity of finite jet
   evaluation realizes every coordinate vector by an actual entire source;
   no abstract replacement source, RH, simplicity or zero-existence premise
   is introduced. The condition budget is measured relative to this explicit
   Taylor norm, not the raw derivative Euclidean norm.

   The native spectral coordinate is `(rho-1/2)*(-I)`. Therefore its squared
   imaginary part is `(Re rho-1/2)^2`: the native minimum is exactly
   `2*m*(Re rho-1/2)^2 + (m-1)/q^2` at frame budget `q^(m-1)`.

The unlimited-budget infimum for a nontrivial chain is the spectral term,
never attained: every finite condition number gives a strictly positive
Jordan penalty, whereas q tends to infinity in the explicit minimizers.
This is a consequence of the same theorem, not another contribution.

### Novelty and significance audit

Closest corpus results already classify when the local Xi matrix is Hermitian
or normal, derive RH/simplicity from positive Hodge symmetry, express D as half
the skew-adjoint HS energy, and bound resolvents under similarity. None gives
this exact attained frontier for every metric budget on the fixed native chain.
NoObstructionOnlyAConstruction chooses a different diagonal model with prescribed
real spectrum; it does not optimize metrics of this fixed defective operator.
The new result combines root-free Schur energy, operator conditioning and actual
arithmetic jets, quantifying the full finite-depth cost hidden by the existing
zero-defect classifiers. All components and the native realization count once.

The latest focused deep query searched 73,150 files / 1,082,670 declarations;
its judge stage was partial after malformed local-model JSON. Available
candidate/source hits and ingredient sets were inspected, followed by direct
source/API verification. Earlier focused searches completed without partial
flags. Compiler/search freshness was mixed. Novelty claimed only against the
audited local corpus, not external literature.

## Verification gates

- [x] Precise universal class and exact attained boundary.
- [x] Source applicability, corpus comparison and complete paper proof.
- [x] All six targeted Lean leaves, primary signatures and axiom lists.
- [x] Wiring and generated index; global lint executed, external failure recorded below.

All six leaves compile with empty logs and are wired once: StrictUpperPowerEnergy,
NilpotentSchurEnergy, GeometricJordanMetricFrame, SharpJordanMetricBudget,
TaylorJordanNormalization and RHTower/XiJordanSharpMetricBudget. Scratch API probes
pass. The audit passed for all 55 explicitly named public declarations,
eight primary signatures, and the three existing native source-realization
theorems: deningerCompactOpenThetaMul_iteratedDeriv',
deningerCompactOpenH1AllJets_theta and deningerCompactOpenFiniteJets_surjective.
All 58 axiom lists are exactly propext, Classical.choice and Quot.sound. All
eleven inspected signatures match their intended unconditional classes; the
native result has no RH, simplicity or source-admission premise.

Index regeneration passed at 03:40 UTC. Global lint --check-generated had one
error: unrelated concurrent RHTower.WeilConePoleDualityAnatomy remained unwired.
No generated-file drift or forbidden-declaration error occurred. The other
381 lines were existing large-file warnings. No unrelated file was changed.
As in the ledger's earlier audits, this external wiring failure is recorded;
global lint is not claimed green. All six owned leaves and imports are verified.
The complete variational classification and native realization count once.

SHA256 of the compiled sources:

```text
StrictUpperPowerEnergy 48c636327961f4f58cb0984b0438e0f31766b69ba5f6c3c4a2ff4780e935dd83
NilpotentSchurEnergy b60ab67f908470c66c17fa445f75f9a5b14d869698fae379c48753ea51c3fb4f
GeometricJordanMetricFrame 6eb9a129693511cd2bf009166b0caf982f4e47068e0f6e28073f68069a10e03b
SharpJordanMetricBudget 90d92a383bcad5ffca0811d0f30fd4c5e7666259c2a1820994066445b65ff5a4
TaylorJordanNormalization a725344617f259d189af6e7a0483e2d015987afc0715eebd9fadcc003f52c96f
XiJordanSharpMetricBudget 6387d600bac202fb1c262621e54f43e294e116ee6f58f7cc8e00686c9057a9ff
```
