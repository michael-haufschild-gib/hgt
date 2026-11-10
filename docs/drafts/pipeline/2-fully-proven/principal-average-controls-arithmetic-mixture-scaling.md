# Principal average controls arithmetic mixture scaling

- **ID:** B130-principal-average-scaling
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean in progress)
- **Source:** [Explicit arithmetic mixture](../3-formalized/arithmetic-two-profile-mixture-with-a-delayed-moving-pole.md), [endpoint moment obstruction](../3-formalized/endpoint-tangent-moment-obstructs-polynomial-scaling.md).

## Statement

Fix an integer `q≥1`. For each reduced residue class `a mod q`, let
`Φ_a` be analytic on a common disc of radius greater than one,
unimodular on `[0,1]`, with `Φ_a(0)=1` and `Φ_a(1)=-1`.
At primes not dividing `q`, use the actual phase `Φ_[p](p^-t)`;
at each prime dividing `q`, choose a profile with the same properties.
Let `L_t` be the resulting Euler product and
`Ψ=(1/φ(q))Σ_a Φ_a`, `Ψ(z)-1=Σ b_k z^k`.

Locally uniformly on `Re w>0`,

`((1+tw)-1)L_t(1+tw)/t² → ζ(2)exp(-Σ_{k≥1}b_k log(w+k))`.

Thus the principal average alone determines the leading scaling;
nonprincipal arithmetic modulation disappears. No joint holomorphic
endpoint germ agrees with these actual Euler products, even if
agreement is required only at nearby positive real parameters and
real spectral values above one.

## Proof

Write `d=φ(q)` and let `χ` range over all characters modulo `q`.
Define the actual finite Fourier profiles

`Dχ(z)=d⁻¹Σ_a χ(a)⁻¹(Φ_a(z)-1)`.

Character orthogonality gives `D₁=Ψ-1` and, at every reduced class,
`Φ_a(z)-1=Σχ Dχ(z)χ(a)`. Each profile is analytic on the common
larger disc. For `χ≠1`, orthogonality gives `Dχ(0)=Dχ(1)=0`.

1. **Exact arithmetic expansion.** For `t≥0`, `Re s>1`, absolute
   Taylor convergence and absolute prime summability justify all
   interchanges. Put `P(s)=Σ_p p^-s` and write `Dχ(z)=Σ_k dχ,k z^k`.
   Then

   `Σ_p(v_p(t)-1)p^-s = Σ_k b_k P(s+kt) + N(t,s)+J(t,s)`,

   `N(t,s)=Σ_{χ≠1}Σ_k dχ,k Pχ(s+kt)`,

   `J(t,s)=Σ_{p|q}(ρ_p(p^-t)-Ψ(p^-t))p^-s`.

   The finite correction is exact: the principal character omits
   ramified primes, whereas `P` includes them. It is `ρ_p-Ψ`, not
   merely the chosen ramified phase.

2. **Nonprincipal terms.** Each `Pχ` has the bounded holomorphic
   horizontal continuation proved in `exists_bounded_characterPrimeLog_tube`.
   A finite intersection supplies a common tube. Nonnegative real
   shifts preserve it. Absolute summability of each Taylor sequence
   gives joint continuity of the shifted sums for real `t≥0`, and
   holomorphy in `s`. Their endpoint values are `Pχ(1)Σ_k dχ,k=0`.
   The finite function `J` is jointly continuous and `J(0,s)=0`.

3. **Principal renormalization.** Let `E(s)=P(s)+log(s-1)` on the
   right half-plane, with its regular value at one. Since `Σ b_k=-2`,
   for `t>0`, `Re w>0`,

   `Σ_k b_k P(1+t(w+k)) = 2 log t - Σ_k b_k log(w+k)`
   `                              + Σ_k b_k E(1+t(w+k))`.

   The final sum is `analyticSmoothingScaledRemainder Ψ 0`.
   Its compact-sector bound requires only analyticity of `Ψ`, not
   unimodularity. It is jointly continuous through `t=0`, with
   endpoint value `2H_triv(1)`.

4. **Higher prime powers and the limit.** Every actual prime phase is
   unitary. On `Re s≥b>1/2`, each higher-power remainder is bounded
   by `2p^(-2b)`. Coordinate continuity and this summable majorant give
   joint continuity of `H_t(s)` for real `t≥0`. At zero all prime
   phases equal `-1`, so `H_0=H_Liouville`. With
   `Z(s)=(s-1)ζ(s)`, the actual quotient `U(t,1+tw)/t²` equals

   `Z(1+tw)exp(-Σ b_k log(w+k)+Σ b_k E(1+t(w+k))`
   `          +N(t,1+tw)+J(t,1+tw)+H_t(1+tw)-H_triv(1+tw))`.

   On every compact subset of `Re w>0`, all displayed factors extend
   continuously to a common compact parameter rectangle. Uniform
   continuity gives locally uniform convergence. At `t=0`, use
   `Z(1)=1`, `N=J=0`, and
   `exp(H_triv(1)+H_Liouville(1))=ζ(2)`. This proves the stated
   principal-average law for the actual Euler product.

5. **Surviving singularity.** The mean is a real affine average of
   normalized unit profiles, so `Re Ψ′(1)=0`. The proved endpoint
   moment theorem supplies `k≥1` with `Re b_k>0` and excludes an
   entire extension of the limiting profile. Its upper continuation
   satisfies `Q(-k+iy)exp(b_k log(iy))→B_k≠0`. Thus the arithmetic
   scaling retains the precise singular shift of its principal mean.

6. **Joint endpoint obstruction.** Suppose a joint holomorphic germ
   agrees with the stated real Euler fibres. Fix a small positive `t`.
   The identity theorem in the spectral variable extends agreement
   from the real interval to the right half-disc; absolute Euler
   convergence supplies spectral holomorphy. Expand the germ at `(0,1)`
   into constant, linear, and quadratic homogeneous Taylor terms plus
   a cubic remainder. Along `(t,1+tw)`, existence of the finite
   quotient limit first forces the constant term to vanish, then the
   linear term on every direction `(1,w)` with `Re w>0` to vanish.
   Dividing the cubic remainder by `t²` makes it tend to zero.
   The limit must equal the quadratic term on `(1,w)`, a polynomial
   in `w` of degree at most two. This contradicts step 5.

All analytic inputs are derived for the actual family; no continuation,
boundedness, or specialization hypothesis is added.

## Formalization inputs

Finite Dirichlet Fourier inversion is already proved by
`RHTower.dirichletCharacterFourier_expansion` in
`RHTower/SelbergClass/DirichletFourier.lean`. Bounded nonprincipal
prime-log continuation and summable shifts are proved in
`GaugeDeformations/CharacterPrimeLogContinuation.lean`.
`analyticPhase_affine_average_no_entire_scaling` excludes an entire
extension of the proposed mean profile.

The existing `continuousOn_analyticSmoothingScaledRemainder` applies
to every analytic mean profile, without a unimodularity condition.
It supplies the principal tail estimate. Finite Fourier inversion
reduces the remaining infinite sums to nonprincipal character profiles
with zero endpoint mass; the ramified correction is `ρ_p-Ψ`.

The scaling proof itself needs only the common endpoint `Φ_a(1)=ρ_p(1)=-1`.
Normalization `Φ_a(0)=1` removes the zeroth mean coefficient and supplies
the singularity obstruction. Values `ρ_p(0)` at ramified primes are irrelevant.

## Significance and boundary

The explicit modulo-four example has a fourth-order shifted zero and
a later second-order pole. The theorem classifies every finite
arithmetic mixture in this analytic profile class, including mixtures with
infinitely many nonzero Taylor coefficients. The positive survivor is
the exact principal-average scaling law. B130's arithmetic Stepanov
estimate remains open.

Corpus searches found the explicit example, the mean-profile
obstruction, and finite Fourier inversion, but no general actual-mixture
scaling theorem. External novelty is unassessed. The paper proof is
dependency-closed; its general arithmetic expansion, scaling, and
endpoint obstruction still require Lean formalization.
