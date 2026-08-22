# The archimedean Gamma--Meixner root scale detects the prime-seam charge

- **ID:** `archimedean-meixner-root-seam-scale`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (paper) / BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source:** Ramanujan's Gamma Fourier transform,
  `SoninSemilocalTwoPlaceAssociation.lean`, `XiPrimeSeamEulerZeroTangent.lean`, and
  `prime-seam-damping-aperture-law.md`
- **Statement:** `[PROVED HERE]` The actual archimedean cyclic Gamma measure is the time-one member
  of a canonical convolution semigroup whose time-`theta` pointed diagonal at the prime logarithms
  is comparable to `p^(-theta)`.  Therefore membership of the reflected Xi seam in every positive
  convolution-time Hilbert domain is equivalent to vanishing of its horizontal charge.  The
  countable subfamily `theta=1/m` already suffices.

## Exact Gamma--Meixner convolution semigroup

For `theta>0`, define the probability measure

```text
dmu_theta(s)
 = 4^(theta/4)/(4*pi*Gamma(theta/2))
     |Gamma(theta/4+i*s/2)|^2 ds.                         (1)
```

Ramanujan's Gamma Fourier formula

```text
integral_R |Gamma(a+i*x)|^2 exp(i*u*x) dx
 = 2*pi*Gamma(2*a)/(4^a cosh(u/2)^(2*a)),   a>0          (2)
```

with `a=theta/4` and `s=2*x` gives

```text
phi_theta(t)
 := integral_R exp(i*t*s) dmu_theta(s)
  = (cosh t)^(-theta/2).                                 (3)
```

At `theta=1`, equation `(1)` is exactly the normalized archimedean cyclic measure already used in
the semilocal corpus:

```text
dmu_1(s)=(2*pi)^(-3/2)|Gamma(1/4+i*s/2)|^2 ds.           (4)
```

Equation `(3)` gives the exact semigroup law

```text
phi_(theta+eta)=phi_theta phi_eta,
mu_(theta+eta)=mu_theta * mu_eta.                         (5)
```

In particular, for every positive integer `m`,

```text
mu_1=(mu_(1/m))^(*m).                                    (6)
```

Thus the inverse powers of `cosh` used below are not arbitrary weights.  They are the unique
convolution roots inside the explicit Gamma--Meixner family containing the actual archimedean
cyclic measure.

## Pointed covariance and its exact prime weight

Let `H_theta=L^2(mu_theta)`, let `U_t` be multiplication by `exp(i*t*s)`, and let `xi_theta=1`.
The stationary characteristic kernel and its pointed diagonal congruence are

```text
<U_t xi_theta,U_u xi_theta>=phi_theta(t-u),

K_theta(t,u)
 =sqrt(phi_theta(2*t)) sqrt(phi_theta(2*u)) phi_theta(t-u). (7)
```

The second kernel is positive semidefinite because it is the Gram kernel of

```text
sqrt(phi_theta(2*t)) U_t xi_theta.                        (8)
```

At a prime logarithm put

```text
w_theta(p)=phi_theta(2*log p).
```

The elementary identity

```text
cosh(2*log p)=p^2(1+p^(-4))/2
```

gives the exact value

```text
w_theta(p)
 =2^(theta/2) p^(-theta)(1+p^(-4))^(-theta/2).           (9)
```

Consequently

```text
p^(-theta)<=w_theta(p)<=2^(theta/2)p^(-theta).           (10)
```

The time-one diagonal is the existing canonical Gamma damping
`semilocalArchimedeanCharacteristic (2*log p)`.  Equation `(9)` constructs its complete positive
convolution-root scale.

## Exact seam-domain threshold

For a complex point `rho` and a rational prime `p`, write

```text
C_p(rho)=orbitwiseNatPrimeSeamCharge p rho.
```

The norm of this value depends only on `sigma=Re(rho)`.  Define

```text
E_theta(rho)=sum_p w_theta(p)|C_p(rho)|^2.                (11)
```

The comparison `(10)` and the already-proved prime-seam damping aperture law give, for every
`theta>0`,

```text
E_theta(rho)<infinity
  iff Re(rho)=1/2 or theta>|2*Re(rho)-1|.                 (12)
```

This is an exact statement, including the boundary.  Off the critical line, equality
`theta=|2*Re(rho)-1|` leaves a positive constant multiple of the divergent prime harmonic series;
the logarithmic seam factor only strengthens the divergence.

## Hilbert--Schmidt formulation

On the prime basis define the channel-resolved synthesis

```text
T_(theta,rho)e_p
 =C_p(rho)sqrt(w_theta(p)) U_(log p)xi_theta.             (13)
```

Whenever it is defined on the complete prime basis,

```text
||T_(theta,rho)||_HS^2=E_theta(rho).                     (14)
```

Thus `(12)` is a source-shaped operator-domain theorem:

```text
T_(theta,rho) is Hilbert--Schmidt
  iff Re(rho)=1/2 or theta>|2*Re(rho)-1|.                 (15)
```

No scalar coherent prime sum is taken.  The full off-diagonal Gamma--Meixner covariance remains in
`T^*T`, while its trace reads the additive diagonal `(11)`.

## Countable RH criterion

For an actual Xi divisor fibre, RH makes every seam charge zero prime by prime.  Conversely, if
`E_(1/m)(rho)` is finite for every positive integer `m`, equation `(12)` gives

```text
|2*Re(rho)-1|<1/m
```

for every `m`, hence `Re(rho)=1/2`.  Therefore

```text
RH
 iff for every rho in Z_Xi and every m>=1,
       T_(1/m,rho) is Hilbert--Schmidt.                  (16)
```

The same conclusion holds for any sequence `theta_n>0` tending to zero.  Multiplicity is retained
by quantifying over the Xi divisor support, although the domain test is fibrewise.

Combining the forward implication in `(16)` with the formal orientation-energy capstone gives the
top-down chain

```text
all Gamma--Meixner root domains contain every Xi seam
  -> every horizontal seam charge vanishes
  -> xiHurwitzOrientationEnergy=0
  -> RH.                                                 (17)
```

## The exact remaining source operation

For `0<theta<1`, equations `(5)` and `(9)` give

```text
w_1(p)=w_theta(p)w_(1-theta)(p).                         (18)
```

The time-one Gamma-damped carrier is already available in the corpus.  Passing from it to the
time-`theta` carrier requires division by the complementary half-density

```text
sqrt(w_(1-theta)(p)) asymptotic to p^(-(1-theta)/2).     (19)
```

This inverse is unbounded on the complete prime basis.  Consequently convolution factorization or
positive definiteness alone does not prove `(16)`.  The live theorem is a source-specific
deconvolution/domain statement for the exact local Euler zero tangent:

```text
for every m>=1, the Xi-zero fibre of
  p |-> d/da|_(a=0) F_(p,s)(a)
belongs to the mu_(1/m) pointed Hilbert--Schmidt domain.  (20)
```

`XiPrimeSeamEulerZeroTangent.lean` already proves that the derivative in `(20)` is exactly
`C_p(s)`.  A proof of `(20)` must come from an Euler--Gamma value relation, a relative trace, or a
source-selected factorization before zero evaluation.  Assuming a zero location, real-rootedness,
or the limiting domain is circular.

## Separation from the Gauss weak-Schatten depth

Connes--Consani's `m`-component Gauss factorization gives Hankel defects of infinitesimal order
`1/(2m)` and critical weak-Schatten exponent `2m`.  That parameter measures singular-number decay
in the Hardy compression.  Equations `(1)`--`(6)` instead vary convolution time in the cyclic
spectral measure and equations `(9)`--`(12)` measure prime-log diagonal decay.  The coincidence of
the symbol `m` does not identify the two constructions.

No current theorem turns Gauss weak-Schatten membership into the root-domain assertion `(20)`.
Such a theorem would have to identify the relevant Gauss-paired pointed overlap with
`phi_(1/m)(2*log p)` or produce an equally strong relative-domain estimate.  The existing
component residue grows in operator regularization depth and does not supply this identification.

## Literature boundary

- Ramanujan's exact Fourier transform is stated and proved for every positive Gamma shape in
  Chakrabarti--Srinivasan,
  [*On a remarkable formula of Ramanujan*](https://arxiv.org/abs/1206.5122).
- The time-one cyclic measure and its semilocal use are in Connes--Consani--Moscovici,
  [*Zeta zeros and prolate wave operators*](https://arxiv.org/abs/2310.18423).
- The distinct Gauss-factor/Hankel construction is in Connes--Consani,
  [*Quasi-inner functions and local factors*](https://arxiv.org/abs/2008.10974).

The Gamma Fourier transform, Meixner convolution semigroup, Gram construction, and prime-series
comparison are standard ingredients.  This card is classified as bridge infrastructure.  Its
contribution is to replace the artificial phrase "all positive prime losses" by one canonical
source-derived convolution-root Hilbert scale and to isolate the unbounded deconvolution that a
proof must control.

## Lean formalization

Status: **complete and unconditional** for every `[PROVED HERE]` equation of this card, `(1)`--`(19)`.
The one remaining item, `(20)`, is the card's own open research.

`formal/GaloisForLFunctions/RHTower/GammaMeixnerRootSeamScale.lean`

- `meixnerChar`, `meixnerChar_pos`, `meixnerChar_zero`, **`meixnerChar_add`**, **`meixnerChar_pow`**
  — the characteristic function `φ_θ(t) = (cosh t)^{-θ/2}`, the semigroup law **`(5)`**, and the
  convolution-root identity **`(6)`** `φ_1 = (φ_{1/m})^m`.
- **`meixnerDensity`**, **`meixnerDensity_eq`** — **equation `(1)`** in its literal form: the
  Lean density `gammaHeightDensity (θ/2) (s/2) / 2` equals
  `4^{θ/4}/(4π Γ(θ/2)) · |Γ(θ/4 + is/2)|²`, constant for constant.
- `meixnerDensity_nonneg`, `integrable_meixnerDensity`, **`integral_cexp_mul_meixnerDensity`**,
  **`integral_meixnerDensity_eq_one`** — **equation `(3)`**: `μ_θ` is a probability measure with
  characteristic function `φ_θ`.  Ramanujan's Gamma Fourier transform **`(2)`** is *not* assumed:
  it is the corpus theorem `GammaEulerPhysicalConnector.fourier_gammaCoshPower_apply`, and the
  passage to the card's variable is a change of variables.  At `θ = 1` this is `(4)`.
- `integrable_cexp_mul_meixnerDensity`, **`isPSDKernel_meixnerChar_sub`** — the stationary
  characteristic kernel `φ_θ(t-u)` is positive semidefinite, by the Bochner computation
  `∑_{j,k} conj(x_j) x_k φ(t_j - t_k) = ∫ |∑_k x_k e^{-i t_k s}|² dμ_θ(s)`.
- `meixnerPointedKernel`, **`isPSDKernel_meixnerPointedKernel`** — **equations `(7)`--`(8)`**: the
  pointed kernel is the Schur product of the rank-one square-root weight kernel with the stationary
  kernel, using the corpus PSD-kernel algebra (`isPSDKernel_rankOne`, `IsPSDKernel.mul`).
- `meixnerPrimeWeight_eq_meixnerChar`, `cosh_two_log_factored`, **`meixnerPrimeWeight_eq`** —
  **equation `(9)`**: `w_θ(p) = 2^{θ/2} p^{-θ} (1+p^{-4})^{-θ/2}`, exactly.  The two-sided
  comparison **`(10)`** is the corpus pair `meixnerPrimeWeight_ge` / `meixnerPrimeWeight_le`
  (`RHTower/PrimeLaplaceGammaJetIncidence.lean`), which already owned the weight itself.
- `meixnerSeamEnergy` — **equation `(11)`**; **`summable_meixnerSeamEnergy_iff`** —
  **equation `(12)`**, the exact root-domain threshold including the boundary, by two-sided
  comparison with the corpus damping-aperture law
  `PrimeSeamDampingAperture.summable_weightedNatPrimeSeamCharge_norm_sq_iff`.
- **`integral_normSq_meixnerSynthesis`**, **`summable_integral_normSq_meixnerSynthesis_iff`** —
  **equations `(13)`--`(15)`**: the squared `L²(μ_θ)` norm of the `p`-th synthesis channel
  `C_p(ρ) √(w_θ(p)) U_{log p} ξ_θ` is exactly `w_θ(p)|C_p(ρ)|²`, so the Hilbert--Schmidt condition
  is `(12)`.
- `re_eq_half_of_forall_meixnerRootDomain`, **`riemannHypothesis_iff_meixnerRootDomain`** —
  **equation `(16)`**, the countable criterion at `θ = 1/m`; **`riemannHypothesis_of_meixnerRootDomain_seq`**
  — the same for an arbitrary positive null sequence of convolution times.
- **`orbitwiseNatPrimeSeamCharge_eq_zero_of_meixnerRootDomain`** — the first arrow of the top-down
  chain **`(17)`**; the remaining arrows are the corpus theorems
  `orbitwiseNatPrimeSeamCharge_eq_zero_iff_re_eq_half` and
  `riemannHypothesis_iff_xiZero_primeClockShale`.
- **`meixnerPrimeWeight_split`** — **equation `(18)`**; **`sqrt_meixnerPrimeWeight_bounds`** —
  **equation `(19)`**, the two-sided form of the complementary half-density asymptotic, which is
  what makes its inverse unbounded on the prime basis.

Every declaration depends only on `propext`, `Classical.choice`, `Quot.sound`.

The `[OPEN]` item `(20)` — root-domain membership of the actual Euler zero tangent — is untouched:
it is the card's own live theorem, not formalization debt.

## Gates

- [x] construct the continuous Gamma--Meixner convolution semigroup containing the actual cyclic
      Gamma measure
- [x] identify the exact prime-log diagonal and compare it two-sidedly with `p^(-theta)`
- [x] prove the exact root-domain threshold and the countable RH consumer
- [x] identify the complementary deconvolution as the missing source operation
- [x] separate convolution time from the Gauss weak-Schatten exponent
- [ ] prove the source-specific root-domain membership `(20)`
- [x] formalize the semigroup weight, threshold, and countable RH consumer in Lean
- [ ] RH

## Log

- 2026-08-22 — Formalized `(1)`--`(19)` unconditionally in Lean; promoted to stage 3.  The
  Ramanujan transform and the two-sided prime weight were already corpus-owned; the new content is
  the semigroup, the literal density constant, the Bochner positivity of the pointed kernel, the
  threshold transfer, and the countable RH consumer.
