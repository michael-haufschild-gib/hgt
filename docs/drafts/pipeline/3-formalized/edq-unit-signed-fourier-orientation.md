# EDQ: signed Fourier orientation at the unit anchor

- **Stage:** 3-formalized
- **RH chain:** literal Euler deletion → actual weighted unit remainder → source comparison of its signed Fourier sectors → exclusion of every off-line zero → RH
- **RH status:** unproved. Individual mode orientation is not the missing comparison of their sum.

## Source question and corpus origin

The linear remainder cutoff controls integer anchors N>=t. At N=1, negative Fourier frequencies can instead have stationary points. The existing exact Bernoulli series and the corpus's monotone sine-transform identity suggest retaining a positive `1-cos` integral for each nonstationary mode. Inspecting `ThetaCuspShellIncompleteGammaCoordinate` shows that its strict sine sign comes from integration by parts and a decreasing weight, not a phase-free norm bound. Apply that mechanism to the actual logarithmic clock and its reciprocal derivative.

## Proved positive source theorem USF

For a>0, beta>1, omega>0, and real gamma with `omega*a+gamma>0`, put

`phi(x)=omega*(x-a)+gamma*log(x/a)`,

`W(x)=x^(1-beta)/(omega*x+gamma)`.

Then `phi(a)=0`, `phi'(x)>0`, and

`-W'(x)=x^(-beta)*[(beta-1)*(omega*x+gamma)+omega*x]/(omega*x+gamma)^2 > 0`

for x>=a. The exact Lean-proved identity is

`integral_a^infinity x^(-beta)*sin(phi(x)) dx`

`= integral_a^infinity [-W'(x)]*(1-cos(phi(x))) dx > 0`.

Paper proof: W tends to zero, its derivative is integrable by monotonicity and its finite endpoint value, and the original power-weighted sine integral is absolutely integrable. Integrate W against the derivative of `1-cos(phi)`. Both boundary products vanish. The right side is nonnegative and strictly positive on an open interval immediately after a, since the phase derivative at a is positive. This keeps the literal power weight.

## Proved literal unit consequences

For sigma>0, t>0, and positive integer k, set beta=sigma+2 and omega=2*pi*k.

- The k-th positive-frequency Bernoulli mode at the unit anchor has strictly positive imaginary part: gamma=t satisfies the source hypotheses at every height.
- The negative-frequency mode has strictly negative imaginary part when `2*pi*k>t`: it is the conjugate of the gamma=-t positive-phase integral.
- Modes with `2*pi*k<=t` retain their entire stationary or boundary-stationary contribution. No integration by a vanishing phase derivative is permitted.

These modes are exactly the `bernoulliFourierTerm` terms already linked to the actual power-sum remainder. Their coefficient is positive for k!=0. The full source still retains its negative mean and both frequency sectors. No term is discarded, and positive representations of separate terms do not orient their signed sum.

## Plan and audit

- [x] Verify reciprocal-clock derivative, positivity, decay, and absolute integrability.
- [x] Prove the exact positive integral identity and strictness.
- [x] Connect both signed sectors to the literal unit-source modes.
- [x] Scratch-check, targeted leaf audits, umbrella wiring, new-declaration axiom audit, lint.
- [ ] Prove the independent comparison of the complete signed unit budget and close RH.

## Exact quantitative survivor and complete source

The density has total mass `integral D = W(a)`, giving

`0 < integral_a^infinity x^(-beta)*sin(phi(x)) dx <= 2*W(a)`.

This bound is valid for every real gamma with `omega*a+gamma>0`; no restriction of height by anchor is used. The negative-frequency phase has a stationary point on `[1,infinity)` exactly when `2*pi*k<=t`. Its exceptional positive integer frequencies form a finite set, contained in `1<=k<=floor(t/(2*pi))`. The equality case stays in that set.

For `g_s(1)=normalizedWeightedRemainder s 1`, sigma>0 and s!=1, the exact absolutely convergent source formula is

`sum_(k in Z) Im(integral_1^infinity bernoulliFourierTerm(k,conj(s),x) dx)`

`= Im(g_s(1)) + t/[12*normSq(s+1)]`.

Thus `Im(g_s(1))` is the complete signed mode sum minus the explicit mean. Neither stationary modes nor either infinite frequency sector is dropped. Knowing that the positive sector is positive and the nonstationary negative sector is negative does not compare their magnitudes. That comparison, including the finite stationary sector, is the remaining source obligation. In particular this theorem does not prove the sharper full-remainder threshold R, C/B2, or RH.

## Formal scope

`formal/GaloisForLFunctions/RHTower/ArithmeticUnitFourierOrientation.lean`, namespace `RHTower.DeletionMixedRefinement`: 31 new declarations, comprising 28 theorems and three definitions.

- `integral_anchoredLogSine_eq_budget`, `integral_anchoredLogSine_pos`, `integral_anchoredLogSine_le`: exact identity, strict sign, and quantitative bound.
- `unit_bernoulliFourierTerm_pos_im_pos`, `unit_bernoulliFourierTerm_neg_im_neg`: literal signed-frequency orientation.
- `hasSum_unit_bernoulliFourierTerm`, `hasSum_unit_bernoulliFourierTerm_im`: complete complex and real unit-source identities.
- `unit_negativeMode_stationary_iff`, `unit_stationaryFrequencies_finite`: exact exceptional-frequency boundary and finiteness.

All declarations were checked together in a foreground scratch. The targeted new leaf build passed in 8.1 seconds; no other leaf or umbrella was rebuilt. Umbrella wiring is present. All 31 new declarations have only `propext`, `Classical.choice`, and `Quot.sound`; no added axioms or computational certificates occur. Formal lint passed, with existing large-file warnings. Only these new declarations were axiom-audited.

Generic ancestry is the existing monotone sine-transform integration-by-parts identity. No literature novelty claim or numerical certificate is made. The sharper full-remainder threshold R, C/B2, and RH remain open unless separately proved.

The separate [stationary-frequency comparison](edq-stationary-frequency-budget.md) sums this positive ceiling and proves the full remainder sign for `t<2*pi*N`, `0<sigma<=1`, `t>=1`. It also retains the finite stationary budget at arbitrary height and proves its positive contribution at every closed-right unit zero. The full R statement beyond that domain, C/B2, and RH remain open.
