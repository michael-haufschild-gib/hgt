# FZZ-P: subtracted negative external Gamma source

- **Stage:** 1-in-progress
- **Type:** closed source-factor theorem; physical source assembly open
- **Predecessor:** [neutral coupling insertion](fzz-p-coupling-insertion-gamma.md)

## Chain and obstacle

Fixed theta/FZZ occurrence → integrated mixed replica–momentum Ward identity in a source-fixed frame → balanced external-Gamma vacuum-delay saturation → passivity → RH.

The neutral insertion gives `Gamma(1+i*p/b)`. The external-leg receiver at `k=4` instead uses real parts `5/2` and `-3/2`. This card attacks the negative-real-part source integral; a complete physical source identification and the mixed Ward producer remain open.

## Candidate and proof mechanism

For `s=-3/2+i*y`, Lean now proves

`integral_0^infinity t^(s-1)*(exp(-t)-1+t) dt = Gamma(s)`.

The exact subtractions are the constant and linear Taylor terms. The remainder is nonnegative; it is bounded by `t^2` for `0<t<=1` and by `t` for all positive `t`. Set `t=exp(x)` and define

`F(x)=exp(s*x)*(exp(-exp(x))-1+exp(x))`,

`G(x)=exp((s+1)*x)*(1-exp(-exp(x)))`,

`H(x)=exp((s+2)*x)*exp(-exp(x))`.

Then `F'=s*F+G` and `G'=(s+1)*G+H`. The first two functions are bounded in norm by `exp(x/2)` on the negative half-line and by `exp(-x/2)` on the positive half-line. The final function is the convergent ordinary Gamma density. Two integrations by parts therefore give `s*integral F=-integral G` and `(s+1)*integral G=-Gamma(s+2)`. The Gamma recurrence yields the claimed value. No numerical experiment is involved.

The proof uses `integral_mul_deriv_eq_deriv_mul_of_integrable`, with every required derivative and integrable product verified. The change `t=exp(x)` is proved on the original positive-ray integral with its Jacobian; complex integrability is also proved. The logarithmic source density is strictly positive everywhere.

For the unmodified radial cutoff

`J_R(y)=integral_(x>-R) exp(s*x)*exp(-exp(x)) dx`,

the exact corrected integral is

`J_R(y)+exp(-s*R)/s-exp(-(s+1)*R)/(s+1)`

`= integral_(x>-R) exp(s*x)*(exp(-exp(x))-1+exp(x)) dx`.

The right side tends to `Gamma(s)` as `R` tends to infinity. This proves the cutoff prescription itself, not merely a convergent replacement defined to have that value. This displayed cutoff theorem uses unit coupling and unit slope.

For arbitrary positive coupling and slope, write `A=exp(u)`, `b=exp(v)` and `s=-3/2+i*p/b`. The original charged subtracted integral is

`I(u,v,p)=integral_R exp(s*b*x)*(exp(-A*exp(b*x))-1+A*exp(b*x)) dx`

`= exp(-s*u)*Gamma(s)/b`.

It is integrable and nonzero for all real `u,v,p`. Its exact logarithmic coupling response is `partial_u I/I=-s`, with real part `3/2`; its derivative is therefore nonzero even at vacuum momentum. This is a derivative of the evaluated original integral, not an unproved interchange of differentiation with an improper cutoff limit.

These results retain both source subtraction and charge-dependent coupling powers. They do not identify the prescription with the complete CFT counterterm or force a complete Ward response to vanish.

## Conjecture, proof, and remaining source test

1. **Negative-real-part Gamma from an actual subtracted integral:** proved in Lean, including positivity, integrability and both integration-by-parts steps.
2. **Same value as the finite part of the original divergent radial integral:** proved in Lean with the exact two cutoff terms.
3. **Neutral coupling-stationarity criterion survives adding the external charge:** fails. The charged logarithmic response has real part `3/2` at every momentum. The surviving positive theorem is the exact normalized response and its nonvanishing, not an exclusion of the FZZ-P route.
4. **Identifying this source prescription with the external-leg factorization:** still open. [Halder–Jafferis, §4, (4.1)–(4.4)](https://arxiv.org/html/2402.00932v3#S4) relates the normalized external vertices to spacelike and timelike Liouville correlators. It describes higher-genus simplification as expected under a further central-charge condition. That discussion does not provide a proved mixed replica–momentum Ward producer at the fixed receiver level.

**Next attack:** derive the complete charged marked-insertion Ward balance, retaining the remaining external leg, nonzero-mode correlator and source normalization. Check an actual source factorization and its replica derivative before importing its cancellation. A new scalar Gamma formula or an assumed coupling independence would not close this gap.

## Plan

- [x] Search current corpus for Taylor bounds, improper integration by parts and Mellin continuation methods.
- [x] Prove the positive remainder bounds and integrability of all three logarithmic integrands.
- [x] Close both integration-by-parts identities, Gamma recurrence and original positive-ray change of variables.
- [x] Prove the exact original cutoff counterterms and their finite-part limit.
- [x] Derive the charged coupling normalization and compare with the actual external-leg arguments; physical source identification remains open.
- [x] Scratch verification, leaf-only final build, umbrella wiring, public-theorem axiom audit and lint.

## Evidence and status

Current corpus inputs inspected and checked in scratch: `Real.norm_exp_sub_one_sub_id_le`; `integral_mul_deriv_eq_deriv_mul_of_integrable`; `Gamma_vertical_eq_fourier`; `aecover_Ioi`; `integral_exp_mul_complex_Ioi`; Haar affine integration. `BarnesSingleZetaContinuation` supplied a different-kernel subtraction template. Deep searches `Mellin integral exponential remainder integration parts boundary gamma negative parameter`, `integrable cutoff lower endpoint tends zero set integral`, `spacelike timelike Liouville cancellation`, and method query `integral_Ioi_mul_deriv_eq_deriv_mul` completed with partial/pending coverage. The method query exposed the actual improper integration-by-parts APIs, which were inspected in source. The Liouville query mostly returned unrelated timelike metric and Liouville-flow results; it gives no corpus-wide absence theorem.

Broad arXiv terms `compensated`, `fragmentation`, `renewal` were searched with 2026 and June–September preferences. The [June 2026 fragmentation fit](https://arxiv.org/abs/2606.16754) supplies no applicable source identity. [Xie–Zhou, 4 September 2026](https://arxiv.org/html/2609.05290v1), Lemma 1, obtains local asymptotics by geometric smoothing of a positive regularly varying sequence, with a scale-separation condition and uniform-integrability control. An attempted transfer to the winding-depth sum would require those actual weights and the matching smoothing law; neither has been derived for the complex marked correlator. Tail asymptotics alone therefore cannot be promoted to the required differentiated local source law here.

Scratch `lake env lean /tmp/fzzp_subtracted_gamma.lean`: PASS with no warnings. Seventeen public theorems have no hypothesis binders. Installed leaf `formal/GaloisForLFunctions/RHTower/FZZCigarSubtractedChargedGamma.lean` is wired into `RHTower.lean`; its proof body exactly matches the checked scratch.

- `lake build GaloisForLFunctions.RHTower.FZZCigarSubtractedChargedGamma`: PASS, only the new leaf compiled, 15 seconds. No umbrella build.
- `lake env lean /tmp/fzzp_subtracted_gamma_axioms.lean`: PASS; all seventeen public theorem dependency closures use only `propext`, `Classical.choice`, `Quot.sound`.
- `python3 scripts/formal_tools.py lint`: PASS, with existing large-file warnings.
- All owned Lean, research and lint processes completed; no stale owned process remains.

Source-factor, cutoff prescription and coupling-response proofs closed. Complete physical source identification and the mixed Ward producer remain open. RH remains unproved.
