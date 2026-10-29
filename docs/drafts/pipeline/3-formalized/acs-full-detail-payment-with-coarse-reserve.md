# Full Haar detail payment with retained coarse Gamma energy

- **ID:** acs-full-detail-payment-with-coarse-reserve
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean verified)
- **Statement:** The full Haar Weil diagonal and its actual Gamma coupling to arbitrary pair averages can be paid together, retaining an arbitrarily large fraction below one of the coarse Gamma energy and a positive logarithmic detail reserve after one fixed detail head.

## Goal

For `F=g+h`, define the literal coupled contribution
`Q(q,d,X)=Γ(F)-Γ(h)+W(h)`.
Here `W(h)` is the original full Weil form on the Haar source, including
every prime power, archimedean mass and its actual pole product. Thus Q
includes the coarse Gamma term and the entire mixed Gamma term.

For every `ε>0`, there is a fixed cutoff A and η>0 such that

`(1-ε)Γ(g)+η Σ log(1/w_a)M_a d_a²+∫h² ≤ Q(q,d,X)-H_{≥3}(q,d,X)`

for all signed coefficients and all horizons with `d_a=0` below A.
This pays the full detail diagonal in the coupled complete source; the
existing Haar floor alone does not retain any prescribed coarse Gamma share.
The term `H_{≥3}` is the literal mixed source of all primes and all exponents
at least three; the pure-detail contributions are already included in W(h).

## Dependency-closed paper proof [PROVED HERE]

Put `κ=1-1/sqrt(2)>0`, `E=exp(1/2)`, `M=∫h²`,
`D=Σ log(1/w_a)M_a d_a²`, `G=Γ(g)`, and `B=Γ(F)-Γ(g)-Γ(h)`.
All masses and Gamma energies are nonnegative by their existing integral
representations. The actual full Haar floor and mixed Gamma bound are
already formalized dependencies.

The verified mixed estimate gives
`B²≤128 exp(1/2) Γ(g)∫h²`, where `B=Γ(F)-Γ(g)-Γ(h)`.
The elementary identity `(εG-CM)²≥0`, with `C=32E/ε`, gives
`B²≤4εG CM≤(εG+CM)²`. Taking nonnegative square roots gives
`B≥-εΓ(g)-(32 exp(1/2)/ε)∫h²`.
The full Haar floor gives
`W(h)≥(1-1/sqrt(2)) Σ log(a)M_a d_a²+(2 gammaHardyPhaseRate(0)-20)∫h²`.
The cell width bound `w_a≥1/(a+1)` gives
`log(1/w_a)≤log(a+1)≤log a+1` for every a≥1. Consequently

`W(h)≥κD-(20-2 gammaHardyPhaseRate(0)+κ)M`.

Since `Q=G+B+W(h)`, for every ε>0 and every q,d,X,

`Q≥(1-ε)G+κD-C_ε M`,

where `C_ε=32E/ε+20-2 gammaHardyPhaseRate(0)+κ`.
This bound has no cutoff assumption and no coarse-mass error.

Choose A≥1 with `(κ/2)log A≥C_ε+1`. For coefficients zero below A,
`(κ/2)D≥(C_ε+1)M`, by the existing bound `log a≤log(1/w_a)`.
Thus `Q≥(1-ε)G+(κ/2)D+M`, uniformly in horizon.

To pay all mixed powers of exponent at least three simultaneously, use the
last inequality with ε/2. Let K be the existing positive constant
`haarGammaUpperConstant`, so `Γ(F)≤2G+8KD`. Set
`δ=min(ε/4,κ/(32K))>0`. The verified higher-power mixed estimate gives
one further fixed cutoff with `|H_{≥3}|≤δΓ(F)`. Take the larger cutoff.
Then

`|H_{≥3}|≤(ε/2)G+(κ/4)D`,

and therefore

`Q-H_{≥3}≥(1-ε)G+(κ/4)D+M`.

Every term is from the original source. This is one joint payment, not
the sum of estimates that each spend the same Gamma reserve.

## Uniform negative dimension [PROVED HERE]

Fix ε=1/2 and its cutoff A. For any finite family of coefficient pairs,
the linear map sending a combination to its first A detail coefficients
has a kernel on which `Q-H_{≥3}≥0`. On any strictly negative subspace,
this map is injective: a nonzero kernel vector would be both negative
and nonnegative. Its target has real dimension A. Thus every such
negative subspace has dimension at most A, uniformly in family and horizon.

## Remaining scope

This is a literal source-component estimate, not a sign or index claim
for the whole Weil form. Coarse prime terms, first-prime mixed terms,
square mixed terms, finite heads and polar cross terms remain explicit.
No claim of compactness for complete low-generator translation orbits.
The earlier square-plus-odd source estimate pays a different collection
of terms. Their reserves cannot be added to infer payment of their union.

## Validation

Paper proof and exact Lean formalization complete in
`ArithmeticIndexDescent/TheFullDetailSourceRetainsCoarseGamma.lean`:

- `fullDetailCoupledSourceForm_eq_source_parts`: literal full-prime and polar source identity.
- `fullDetailCoupledSourceForm_ge`: arbitrary-coefficient estimate with detail mass error only.
- `exists_fullDetailCoupled_coarse_reserve`: fixed-head payment retaining any coarse share below one.
- `exists_fullDetailHigherMixed_coarse_reserve`: simultaneous payment of all mixed exponents at least three.
- `exists_fullDetailHigherMixed_uniform_tail`: unconditional formulation for all tail coefficients and horizons.
- `exists_uniform_fullDetailHigherMixed_negative_dimension`: uniform negative dimension at most A on every finite family.

Final check passed with no diagnostics:
`lake --old env lean GaloisForLFunctions/ArithmeticIndexDescent/TheFullDetailSourceRetainsCoarseGamma.lean`.
The module is wired into the ArithmeticIndexDescent umbrella; the umbrella
was not compiled. No dependency oleans needed rebuilding.

No web search, novelty checks, numerical experiments or axiom checks.
