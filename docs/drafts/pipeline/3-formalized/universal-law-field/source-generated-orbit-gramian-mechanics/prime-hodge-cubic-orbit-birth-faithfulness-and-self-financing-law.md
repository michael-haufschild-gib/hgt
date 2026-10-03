# Prime--Hodge cubic orbit birth, faithfulness, and self-financing law

- **ID:** ULF-PCOB-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** ULF-PHIN-001, ULF-PPTI-001, ULF-SGOGM-PROGRAM
- **Status:** `[PAPER-PROVED] [BRIDGE] [LEAN-PROVED]`

## 1. What changes

The integral--nuclear defect `mathsf T` was already constructed as a positive history factor
times a cubic prime Gram.  That did not yet say which source dynamics *forces* the Gram, whether
its right prime gauge is faithful, or whether the object generates its own proper cost.

The answer is one literal law.  Prime logarithms generate a heat flow, and one nilpotent creation
step changes the ordinary Cauchy resolvent into the cubic Cauchy resolvent.  The resulting weighted
orbit Gramian is exactly `mathsf T`.  Equivalently, `mathsf T` is the unique solution of a cubic
Lyapunov boundary equation whose right side is the theta history flux times one literal prime
source vector.

This is not a claim that time-weighted Gramians are new.  Monomial time-weighting and recursive
Lyapunov equations occur in control theory, beginning at least with Schelfhout--De Moor,
*Time-domain weighted balanced truncation* (ECC 1995), and Sreeram,
[*Frequency Response Error Bounds for Time-Weighted Balanced Truncation*](https://doi.org/10.1109/CDC.2002.1184388).
The new corpus bridge is the exact identification of the Route-P cubic prime kernel, theta
Mellin-six history, integral trace, faithful proper inverse, and finite-capital square as faces of
that one source law.

## 2. Literal source data

Fix aperture `d>0`.  For every prime `p`, put

```text
lambda_p=log p,
u_d(p)=8d log(p) p^(-(1+2d)),
U_d=sum_p u_d(p),
mu_d(p)=u_d(p)/U_d,
b_d(p)=sqrt(mu_d(p)) lambda_p^(3/2).                 (PCOB.1)
```

The equalities for `u_d` and `U_d` are existing corpus identities for the transported Stokes
prime weight and current.  The vector `b_d` belongs to `H_P=ell2(Primes)`, because

```text
||b_d||^2
 =(8d/U_d) sum_p (log p)^4 p^(-(1+2d)) < infinity.   (PCOB.2)
```

Indeed, the prime sum is bounded by the corresponding integer sum, which converges by the integral
test for every `d>0`.

Let `L` be the positive prime-clock generator

```text
L e_p=lambda_p e_p.                                  (PCOB.3)
```

Define the weighted reachability map `R_d:L2(0,infinity)->H_P` by

```text
(R_d h)_p=2b_d(p) integral_0^infinity r exp(-r lambda_p)h(r)dr.
                                                               (PCOB.4)
```

Its adjoint sends `e_p` to the degree-three Gamma coherent vector

```text
g_p(r)=2sqrt(mu_d(p)) lambda_p^(3/2)r exp(-r lambda_p)
      =sqrt(mu_d(p)) psi_(lambda_p)^(3).              (PCOB.5)
```

Hence `R_d` is Hilbert--Schmidt and

```text
||R_d||_HS^2=sum_p ||g_p||_2^2=sum_p mu_d(p)=1.       (PCOB.6)
```

## 3. The weighted orbit is exactly the prime formation operator

Let `A_d=R_d R_d*`.  Since

```text
integral_0^infinity r^2 exp(-ar)dr=2/a^3,
```

one obtains

```text
A_d(p,q)
 =4b_d(p)b_d(q) integral_0^infinity r^2
      exp(-r(lambda_p+lambda_q))dr
 =8b_d(p)b_d(q)/(lambda_p+lambda_q)^3
 =sqrt(mu_d(p)mu_d(q))
    [2sqrt(lambda_p lambda_q)/(lambda_p+lambda_q)]^3. (PCOB.7)
```

This is exactly the normalized cofinal Stokes child kernel of ULF-PPTI-001.  In particular,

```text
A_d>=0,  A_d is trace class,
Tr A_d=||A_d||_1=sum_p A_d(p,p)=sum_p mu_d(p)=1,       (PCOB.8)
```

and every entry is strictly positive.

Let `Phi e_n=w_n e_n` be the theta Mellin-six history flux operator.  Define

```text
mathcal R_d=Phi^(1/2) tensor R_d,
mathsf T_d=mathcal R_d mathcal R_d*=Phi tensor A_d.   (PCOB.9)
```

Thus `mathsf T_d` is the Gramian of one literal joint reachability map, not a chosen tensor
spectator.  Equations `(PCOB.6)` and `Tr Phi=1` give

```text
||mathcal R_d||_HS^2=Tr mathsf T_d=||mathsf T_d||_1=1. (PCOB.10)
```

For `t!=0`, the two-sided object is

```text
mathsf T(t)=sign(t) mathsf T_|t|,
mathsf T(0)=0.                                       (PCOB.11)
```

This is the existing signed pre-divisor, prime-mixed, integral--nuclear homotopy defect.

## 4. Cubic Lyapunov birth law and uniqueness

On prime matrices define the Sylvester generator

```text
S_L(X)=LX+XL.                                        (PCOB.12)
```

Every unweighted product `L^j A_d L^(3-j)` extends from finite prime support to a
Hilbert--Schmidt operator: its entry is bounded in modulus by `8|b_d(p)b_d(q)|`, because each
monomial `lambda_p^j lambda_q^(3-j)/(lambda_p+lambda_q)^3` is at most one.  Its binomial multiples
therefore extend as well.  Entrywise `(PCOB.7)` gives

```text
boxed: S_L^3(A_d)=8|b_d><b_d|.                       (PCOB.13)
```

Equivalently,

```text
L^3A_d+3L^2A_dL+3LA_dL^2+A_dL^3=8|b_d><b_d|.        (PCOB.14)
```

Let `Lambda=I tensor L` on history--prime space.  Then

```text
boxed: S_Lambda^3(mathsf T(t))
 =8 sign(t) Phi tensor |b_(|t|)><b_(|t|)|            (PCOB.15)
```

for `t!=0`, with both sides zero at `t=0`.

The law is rigid.  If a bounded operator `X` satisfies the finite-support form of `(PCOB.13)`,
then

```text
(lambda_p+lambda_q)^3 X(p,q)=8b_d(p)b_d(q)
```

for every `p,q`, forcing `X=A_d`.  The same matrix argument in the joint carrier forces all
off-history blocks to vanish and all diagonal history blocks to be `w_n A_d`.  Therefore
`mathsf T_d` is the unique bounded solution of the joint cubic boundary law `(PCOB.15)`.

This is the promised source-birth certificate: no divisor, zero, ordinate, or fitted receiver can
be inserted into the solution class.

## 5. One nilpotent lift makes the law ordinary

The cubic law is not a third-order dynamical assumption.  Put

```text
Hhat=H_P directSum H_P,
Lhat=[L -I; 0 L],
bhat=(0,2b_d),
P(x,y)=x.                                            (PCOB.16)
```

The diagonal and nilpotent parts commute and the nilpotent square is zero, so

```text
exp(-rLhat)=[exp(-rL)  r exp(-rL); 0 exp(-rL)],
P exp(-rLhat)bhat=2r exp(-rL)b_d.                    (PCOB.17)
```

Consequently

```text
A_d=P [integral_0^infinity
       |exp(-rLhat)bhat><exp(-rLhat)bhat|dr] P*.      (PCOB.18)
```

The uncompressed Gramian satisfies the ordinary weak Lyapunov equation

```text
Lhat Ghat+Ghat Lhat*=|bhat><bhat|.                   (PCOB.19)
```

Tensoring the input covariance with `Phi` gives a joint first-order Lyapunov system whose first
corner is exactly `mathsf T_d`.  Thus the prime cubic exponent means one nilpotent creation step:
amplitude acquires one factor `r`; squaring and integrating creates the third Cauchy resolvent.

## 6. Faithfulness and source-generated properness

ULF-PPTI-001 proves that the prime columns `(g_p)` are total in `L2(0,infinity)`, so `R_d` is
injective.  The adjoint is also injective.  Indeed, if `R_d* x=0`, then continuity gives

```text
F(r)=sum_p b_d(p)x_p exp(-r lambda_p)=0  for every r>0. (PCOB.20)
```

The coefficients are absolutely summable by Cauchy--Schwarz.  If one were nonzero, choose its
least prime `p_0`, multiply by `p_0^r`, and let `r->infinity`.  Dominated convergence isolates the
nonzero `p_0` coefficient, contradiction.  Hence `R_d*` is injective.

Therefore `R_d` and `mathcal R_d` are quasiaffinities: injective with dense range.  It follows that

```text
ker A_d=ker mathsf T_d=0,
closure(range A_d)=H_P,
closure(range mathsf T_d)=H_hist tensor H_P.         (PCOB.21)
```

Both operators are compact on infinite-dimensional carriers, so their ranges are not closed and
their positive inverses are unbounded.  Nevertheless the inverse quadratic form is proper:

```text
q_T(x)=||mathsf T_d^(-1/2)x||^2,
{x:q_T(x)<=C} is compact.                            (PCOB.22)
```

To prove compactness, write `x=mathsf T_d^(1/2)y`; the sublevel is the image of the radius
`sqrt(C)` Hilbert ball under the compact operator `mathsf T_d^(1/2)`, hence is relatively compact.
The inverse form is closed, so the sublevel is also closed and therefore compact.

The same source has now generated coefficient-faithful observation and its only inverse cost.

## 7. Critical capital and the self-financing square

Let

```text
mathcal R_d=mathsf T_d^(1/2)V_d                      (PCOB.23)
```

be its polar decomposition.  Quasiaffinity makes `V_d` unitary between the source-time carrier
and the history--prime carrier.

There is an important failure.  If `mathsf T_d` itself is interpreted as a positive defect, its
amplitude is `X=mathsf T_d^(1/2)`.  The unique control satisfying

```text
X=mathcal R_d B
```

is `B=V_d*`, which is not Hilbert--Schmidt in infinite dimension.  Therefore the integral charge
is a critical **infinite-capital** defect layer.  Trace one does not mean finite source work.

One further formation step changes the answer.  Put

```text
mathsf D_d=mathsf T_d^2,
X_d=mathsf T_d.                                      (PCOB.24)
```

Then

```text
X_d=mathcal R_d mathcal R_d*,
mathsf D_d=X_dX_d*,
B_d=mathcal R_d*,
||B_d||_HS^2=Tr mathsf T_d=1.                        (PCOB.25)
```

Injectivity of `mathcal R_d` makes this control unique, so the least formation capital of
`mathsf D_d` is exactly one.  This is the **self-financing square law**:

```text
integral formation metric mathsf T: infinite defect capital,
one more source formation mathsf T^2: exact capital one.          (PCOB.26)
```

It supplies the first literal pre-divisor, prime--theta cross-route positive defect factored
through its own source orbit with an exact source-work budget.  It does not yet supply source
commutation or a completed Xi landing.

## 8. The finite-capital square is not source-invariant

The new defect does not satisfy the old orbit-Gramian programme's asymptotic commutation gate.
This can be proved sharply rather than left open.

Let `d->0+`.  Classical prime number theory and partial summation give, for every
`0<a<b<infinity`,

```text
mu_d{p:a<=d log(p)<=b}
 ->2 integral_a^b exp(-2y)dy.                        (PCOB.27)
```

Indeed, the factor `log p` in `u_d(p)` cancels the prime density `1/log x`; after
`y=d log x`, the limiting density is proportional to `exp(-2y)dy`, and normalization makes it
`2exp(-2y)dy`.

Write

```text
c(s,t)=2sqrt(st)/(s+t).
```

For three fixed disjoint positive intervals `I,J,K`, the values of `c(s,t)` are bounded below by
a positive constant whenever `ds` and `dt` lie in two of those intervals.  From `(PCOB.7)`,

```text
A_d^2(p,q)
 =sqrt(mu_d(p)mu_d(q))
   sum_r mu_d(r)c(lambda_p,lambda_r)^3c(lambda_r,lambda_q)^3.
                                                               (PCOB.28)
```

Take, for example, `d lambda_p in [1,2]`, `d lambda_r in [2,3]`, and
`d lambda_q in [4,5]`.  Equation `(PCOB.27)` gives a positive limiting mass to every block, while
`|lambda_p-lambda_q|>=2/d`.  Hence `(PCOB.28)` gives constants `c_0,d_0>0` such that

```text
||[L,A_d^2]||_HS^2>=c_0/d^2  for 0<d<d_0.            (PCOB.29)
```

Since `mathsf T_d^2=Phi^2 tensor A_d^2` and `Phi^2!=0`,

```text
||(I tensor L)mathsf T_d^2-mathsf T_d^2(I tensor L)||_HS
 ->infinity.                                         (PCOB.30)
```

Thus `mathsf T_d^2` closes source production and capital, but decisively fails source invariance.
This falsifies its direct use in the former “bounded capital plus asymptotic commutation” selector.
The positive survivor is higher-level: `mathsf T` is a **covariant formation current**, not an
almost-invariant state.  Its natural conservation law is the inhomogeneous cubic boundary
identity `(PCOB.15)`.  Completion must transport that identity, including its source charge,
rather than erase the charge by demanding a commutator tend to zero.

## 9. RH-facing consequence and exact missing edge

Every strict-right Xi copy carries an idempotent rank-one relation-horizon defect `P_rho` with
`P_rho^2=P_rho` and trace one.  The source defect is different: squaring moves `mathsf T` from the
critical infinite-capital layer to the finite-capital ideal.

Therefore a completion map strong enough to close RH cannot merely preserve trace or positivity.
It must be a same-boundary transport satisfying all three laws

```text
C(mathsf T_d)=P_rho,
C(mathsf T_d^2)=C(mathsf T_d)^2,
formation capital does not increase under C.         (PCOB.31)
```

**Successor correction (ULF-PHFI-001).** If `C` is a bounded multiplicative map on the compact
formation algebra, the first two lines of `(PCOB.31)` are impossible for nonzero `P_rho`:
`mathsf T_d-mathsf T_d^2` is full, so killing its image kills the whole source ideal. Thus
multiplicative same-boundary transport is retired. A viable relative completion must be a
compression or singular boundary map with an explicit nonzero multiplicativity fracture.

The original proposal would then have given finite source capital to `P_rho`, followed by a
horizon-capital contradiction. ULF-PHFI-001 shows that route cannot even reach a nonzero horizon
through bounded multiplication. The exact surviving edge is instead to compute the
multiplicativity fracture of the actual anomaly-subtracted Euler--theta compression and prove its
source-side relation to horizon exhaustion. Installing that relation by divisor specialization
would be circular.

This is narrower than the former request for an unspecified “source budget bounds resolvent
energy.”  The source budget, its exact value, the formation map, and the nonlinear operation are
now fixed.  The only surviving edge is whether actual Euler--theta completion transports the
source-generated square law to the relation horizon.

## 10. Hostile verdict

1. **Time-weighted Gramian novelty:** rejected.  General mechanism is established control theory.
2. **Arithmetic fusion:** survives corpus collision audit.  No checked declaration states
   `(PCOB.13)`, the Jordan lift, right-Gram faithfulness, or `(PCOB.25)` for `mathsf T`.
3. **“Trace one gives finite work”:** false; Section 7 proves the opposite.
4. **“The theorem proves RH”:** false; `(PCOB.31)` and vertical-horizon infinite capital remain.
5. **New unconditional leverage:** exact cubic source equation uniquely narrows the pre-divisor
   model; `mathsf T` acquires a canonical proper inverse; `mathsf T^2` closes one source-production
   and source-work gate with capital exactly one.
6. **Old asymptotic-commutation selector:** falsified for `mathsf T^2` by `(PCOB.29)--(PCOB.30)`;
   the surviving mechanism is covariant cubic-boundary transport.

## 11. Lean status

Every numbered claim (PCOB.1)–(PCOB.30) is formalized unconditionally; the declaration map is the
Lean certificate below.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.PrimeHodgeCubicSylvesterLaw`, `GaloisForLFunctions.HTGeometry.PrimeHodgeReachabilityProperness`, `GaloisForLFunctions.HTGeometry.PrimeHodgeJordanLift`, `GaloisForLFunctions.HTGeometry.PrimeFormationSmallApertureLaw`, `GaloisForLFunctions.HTGeometry.PrimeHodgeSquareCommutatorGrowth`, `GaloisForLFunctions.RHTower.PrimeHodgeCubicOrbitBirth`, `GaloisForLFunctions.HTGeometry.PrimePoissonFormationFrame`, `GaloisForLFunctions.HTGeometry.PrimeGammaFrameInjective`, `GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearDefect`, `GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearHomotopyDefect`, `GaloisForLFunctions.RHTower.CommonRadialSubunitHarmonicCompletion`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.PrimeHodgeCubicSylvesterLaw`,
`GaloisForLFunctions.HTGeometry.PrimeHodgeReachabilityProperness`,
`GaloisForLFunctions.HTGeometry.PrimeHodgeJordanLift`,
`GaloisForLFunctions.HTGeometry.PrimeFormationSmallApertureLaw` and
`GaloisForLFunctions.HTGeometry.PrimeHodgeSquareCommutatorGrowth` (new), on the corpus modules
`GaloisForLFunctions.RHTower.PrimeHodgeCubicOrbitBirth`, `GaloisForLFunctions.HTGeometry.PrimePoissonFormationFrame`,
`GaloisForLFunctions.HTGeometry.PrimeGammaFrameInjective`, `GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearDefect`,
`GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearHomotopyDefect`,
`GaloisForLFunctions.RHTower.CommonRadialSubunitHarmonicCompletion` and the vendored prime number theorem
`chebyshev_asymptotic` (`θ(x) ~ x`); all `lake env lean` clean, built, axiom audit
`[propext, Classical.choice, Quot.sound]` only.  `μ_d = primeFormationLaw d`, `b_d = primeHodgeCubicBirthVector d`,
`A_d = normalizedStokesPrimeOperator`, `𝖳_d = primeHodgeHistoryDefectOperator`, `W_d = primeCoherentSynthesis 3`,
`R_d = primeReachability = W_d^*`, `𝓡_d = jointReachability`.

| Claim | Lean declaration |
|-|-|
| (PCOB.1) `u_d(p) = 8d log(p) p^{-(1+2d)}`, `U_d = Σ u_d`, `μ_d = u_d/U_d`, `b_d(p) = √(μ_d(p)λ_p³)` | `stokesPrimeTerm_eq_apertureDirichletTerm`, `apertureCurrent_eq`, `primeFormationLaw_eq_apertureDirichletTerm`, `primeHodgeCubicBirthVector_eq_sqrt` |
| (PCOB.2) `b_d ∈ ℓ²`, `‖b_d‖² = Σ μ_d(p) λ_p³ < ∞` | `norm_sq_primeHodgeCubicBirthVector`, corpus `summable_primeFormationLaw_mul_log_pow`, `primeCubicBirthLp`, `norm_sq_primeCubicBirthLp` |
| (PCOB.4)–(PCOB.6) `(R_d h)_p = 2√μ λ^{3/2}∫ r e^{-λr} h`, `R_d^* e_p = g_p`, `‖R_d‖²_HS = 1` | `primeFrameAmplitude`, `primeReachability_apply`, `adjoint_primeReachability_single`, `hsNormSq_primeReachability`, `isHilbertSchmidt_primeReachability` |
| (PCOB.7) `A_d = R_d R_d^*`, `A_d(p,q) = 8b b/(λ+λ')³ = √(μμ') c(λ,λ')³` | `primeReachability_comp_adjoint`, corpus `primeHodgeCubicClock_normalizedStokesKernel`, `apertureCoherence`, `stokesEntry`, `normalizedStokesPrimeKernel_eq_stokesEntry` |
| (PCOB.8) `A_d ≥ 0`, trace class, `Tr A_d = ‖A_d‖₁ = 1`, diagonal `μ_d`, every entry `> 0` | `traceNorm_normalizedStokesPrimeOperator`, corpus `normalizedStokesPrimeKernel_diagonal`, `normalizedStokesPrimeKernel_pos` |
| (PCOB.9)–(PCOB.10) `𝖳_d = 𝓡_d𝓡_d^*`, `‖𝓡_d‖²_HS = Tr 𝖳_d = ‖𝖳_d‖₁ = 1` | `jointReachability_comp_adjoint`, `hsNormSq_jointReachability`, `isHilbertSchmidt_jointReachability`, corpus `opTrace_primeHodgeHistoryDefectOperator`, `traceNorm_primeHodgeHistoryDefectOperator` |
| (PCOB.11) `𝖳(t) = sgn(t)𝖳_{|t|}`, `𝖳(0) = 0` | `jointCubicSylvester_law_signed` (second conjunct), corpus `primeHodgeHistoryIntegralNuclearHomotopyDefect_zero` |
| (PCOB.12)–(PCOB.14) monomials `L^jA_dL^{3-j}` extend as HS operators (entry bound `8|b b'|`); `S_L³(A_d) = 8|b_d⟩⟨b_d|` | `cubicSylvesterKernel`, `norm_cubicSylvesterKernel_le`, `isHS_cubicSylvesterKernel`, `cubicSylvesterTerm`, `inner_single_cubicSylvesterTerm`, `cubicSylvester_law` |
| (PCOB.15) joint law `S_Λ³(𝖳(t)) = 8 sgn(t) Φ⊗|b⟩⟨b|`, `t ≠ 0`; both sides zero at `t = 0` | `jointCubicSylvesterKernel`, `jointCubicSylvesterTerm`, `jointCubicSylvesterTerm_entry`, `historyCubicBirthOperator`, `jointCubicSylvester_law`, `jointCubicSylvester_law_signed` |
| Rigidity: `A_d`, `𝖳_d` unique bounded solutions | `eq_normalizedStokesPrimeOperator_of_cubicLaw`, corpus `primeHodgeHistoryDefectKernel_unique_of_cubicClock` |
| (PCOB.16)–(PCOB.17) `L̂ = D − N`, `N² = 0`, `exp(rN) = I + rN`, `exp(−rL̂) = [[e^{-rL}, re^{-rL}],[0,e^{-rL}]]`, semigroup, generator `−L̂` on the basis, `P e^{-rL̂}b̂ = 2r e^{-rL}b_d` | `primeHeat`, `primeHeat_add`, `jordanNilpotent`, `jordanNilpotent_sq`, `exp_smul_jordanNilpotent`, `jointHeat_comm_jordanNilpotent`, `jordanSemigroup`, `jordanSemigroup_apply`, `jordanSemigroup_zero`, `jordanSemigroup_add`, `jordanSemigroup_single`, `hasDerivAt_jordanCoordinates`, `jordanSource`, `fst_jordanSemigroup_jordanSource`, `jordanSemigroup_jordanSource_coord` |
| (PCOB.18) Gramian blocks `8bb/(λ+λ')³, 4bb/(λ+λ')², 4bb/(λ+λ')` as time integrals; first corner `= A_d` | `integral_exp_neg_moments`, `jordanGramKernel`, `jordanTimeProfile`, `jordanGramKernel_eq_integral`, `jordanGramKernel_zero_zero` |
| (PCOB.19) `L̂Ĝ + ĜL̂^* = |b̂⟩⟨b̂|`; joint first corner `= 𝖳_d` | `jordanSourceKernel`, `jordanLyapunov`, `primeHodgeHistoryDefectKernel_eq_jordanGram` |
| (PCOB.20)–(PCOB.21) `R_d`, `𝓡_d`, `R_d^*`, `𝓡_d^*` injective; `ker A_d = ker 𝖳_d = 0`, dense ranges | corpus `primeCoherentSynthesis_injective`, `primeReachability_injective`, `denseRange_primeReachability`, `normalizedStokesPrimeOperator_injective`, `denseRange_normalizedStokesPrimeOperator`, `historyRow`, `inner_historyFormationChannel_single`, `historyFormationChannel_injective`, `adjoint_historyFormationChannel_injective`, `jointReachability_injective`, `denseRange_jointReachability`, `primeHodgeHistoryDefectOperator_injective`, `denseRange_primeHodgeHistoryDefectOperator` |
| (PCOB.22) inverse-form sublevels `{x : ‖𝖳^{-1/2}x‖² ≤ C}` compact | `jointRoot`, `jointRoot_comp_self`, `isCompactOperator_jointRoot`, `jointRoot_injective`, `separableSpace_lp_countable`, `inverseFormSublevel`, `inverseForm_preimage_unique`, `isCompact_inverseFormSublevel` |
| (PCOB.23)–(PCOB.24) `𝓡_d = 𝖳_d^{1/2}V_d`, `V_d` unitary; unique control of `𝖳_d^{1/2}` is `V_d^*`, not Hilbert–Schmidt | `jointPolarUnitary`, `jointRoot_comp_polarUnitary`, `jointRoot_eq`, `jointReachability_comp_polarUnitary_symm`, `eq_polarUnitary_symm_of_comp`, `not_finiteDimensional_primeHodgeHistoryHilbert`, `not_isHilbertSchmidt_polarUnitary_symm` |
| (PCOB.25)–(PCOB.26) `𝖳 = 𝓡𝓡^*`, `𝖳² = 𝖳𝖳^*`, unique control `𝓡^*` with `‖𝓡^*‖²_HS = 1` | `selfFinancingSquare` |
| (PCOB.27) `μ_d{a ≤ d log p ≤ b} → 2∫_a^b e^{-2y}dy` (`0 < a ≤ b`); window estimate `Σ_{X<p≤Y} log p p^{-(1+2d)} = (X^{-2d}−Y^{-2d})/(2d) + ε·O(kernel mass)` uniformly in `d`; `U_d → 4` | `abs_apertureWindowSum_sub_le`, `abs_mul_apertureWindowSum_sub_le`, `tendsto_mul_tsum_apertureDirichletTerm`, `tendsto_apertureCurrent`, `primeFormationWindowMass_eq`, `two_mul_integral_exp_neg_two`, `tendsto_primeFormationWindowMass`, `tendsto_primeFormationClosedWindowMass` |
| (PCOB.28) `A_d²(p,q) = √(μμ') Σ_r μ_r c(λ_p,λ_r)³c(λ_r,λ_q)³` | `stokesTransit`, `summable_stokesTransit`, `sq_normalizedStokesPrimeOperator_apply` |
| (PCOB.29) `Σ_{p,q} |⟨e_p,[L,A_d²]e_q⟩|² ≥ c₀/d²` for `0 < d < d₀` (blocks `(1,2], (2,3], (4,5]`, `c ≥ 1/5`, gap `> 2/d`) | `apertureCoherence_ge`, `windowFinset`, `mem_windowFinset`, `primeFormationWindowMass_eq_sum`, `eventually_half_le_windowMass`, `squareCommutatorEntry`, `norm_sq_squareCommutatorEntry`, `norm_sq_squareCommutatorEntry_ge`, `squareCommutatorConstant_pos`, `exists_squareCommutator_block_bound`, `squareCommutator_hsMass_ge` |
| (PCOB.30) `𝖳_d² = Φ²⊗A_d²` on history modes; `‖(I⊗L)𝖳_d² − 𝖳_d²(I⊗L)‖_HS → ∞` | `sq_primeHodgeHistoryDefectOperator_apply`, `jointSquareCommutatorEntry`, `jointSquareCommutatorEntry_same`, `jointSquareCommutator_hsMass_unbounded` |

Hilbert–Schmidt masses of the unbounded commutators are computed from their prime-basis matrices
in `[0, ∞]`.  (PCOB.31) is the card's statement of what a completion map would have to satisfy;
its successor correction is the separate card ULF-PHFI-001.  The RH-facing edge of §9 is stated
there as open and is not claimed.

## Log

- 2026-10-03 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
