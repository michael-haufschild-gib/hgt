# CLG/TTF complete two-atom middle-source control

- **Stage:** 3-formalized
- **Scope:** Exact two-atom source and reflection model, complete infinite remainder bounds through derivative ten, and compensation-source bounds on the remaining middle interval.
- **Full chain:** Literal theta source → all signed center-mixed jet Hankel sections nonnegative → global Fourier-current sign → Xi Bezoutian orientation → RH.
- **Remaining:** The compensated odd determinant comparison on `(8/95,7/16)`, then the all-order hierarchy. No global rank-six or RH conclusion is claimed.

## Literal source and calibrated deep tail

Write `q=π exp(2x)`, `B=q−3/2`, `φ=thetaCuspSourceTerm x 1`, `Φ=thetaCuspFullSource`, and `T=thetaCuspSourceTerm x 1+thetaCuspSourceTerm x 2`. The existing positive likelihood measure splits exactly into the second-atom measure and the complete deep measure, summing every atom `n≥3`. Its support is contained in `[8,∞)`.

For `M_d(B,m)=∫t^m exp(−Bt) dμ_d(t)`, Lean proves

`M_d(19/20,0)≤10⁻⁶`.

This is an infinite-series bound. At the calibration point, the atom with index `n=k+3` is bounded by

`3n⁴ exp(−(49/20)(n²−1))`.

The elementary inequalities `n⁴≤81·4^k` and `n²−1≥8+7k` reduce its sum to

`243 exp(−98/5) Σ_k(1/25)^k`.

The exponential factors are bounded using proved rational lower bounds on `exp(1)`, `exp(3/5)` and `exp(5)`. In particular `exp(98/5)≥260000000`, and the displayed geometric sum is below one millionth. All arithmetic identities and inequalities are proved symbolically in Lean; no evaluated theta sum is a premise.

Define

`δ(x)=exp(−8(q−49/20))/1000000`.

The exact support comparison gives

`M_d(B,m)≤8^m δ(x)` whenever `m/8≤q−49/20`.

In particular this holds for `m≤10`, `q≥37/10`. A quadratic exponential lower bound and `π>3.14` prove that `x≥8/95` implies `q≥37/10`. Thus this regime covers every point of the remaining center interval.

## Complete derivative error

Set `E(x)=M_d(B(x),0)`. The weighted moments `J_(0,m)=q^m M_d(B,m)` satisfy the actual source derivative recurrence

`J_(n+1,m)=2m J_(n,m)−2J_(n,m+1)`.

The existing signed scalar cooling polynomial bound applies to `qt≥8q≥18`. Integrating it against the complete positive deep measure and applying the support estimate gives

`0≤(−1)^n E⁽ⁿ⁾(x)≤(16q)^n δ(x)` for `n≤10`, `q≥37/10`.

The exact second-atom ratio identifies the full source error:

`Φ−T=φE`.

Smoothness follows locally from this quotient identity and strict positivity of `φ`. Every derivative therefore retains the complete tail:

`Φ⁽ⁿ⁾−T⁽ⁿ⁾=Σ_i binom(n,i) φ⁽ⁱ⁾ E⁽ⁿ⁻ⁱ⁾`.

Its absolute bound is `δ Σ_i binom(n,i)|φ⁽ⁱ⁾|(16q)^(n−i)` through order ten.

## Reflection before absolute values

Let `A=T/φ`, and let `f_±=f(x±t)`. Exact local factorization gives

`Φ_+Φ_−−T_+T_−=φ_+φ_− V`,

`V=A_+E_−+E_+A_−+E_+E_−`.

Writing `b_i=D_t^i[φ_+φ_−](0)`, `j_n=D_t^n[Φ_+Φ_−](0)` and `t_n=D_t^n[T_+T_−](0)`, the literal all-order identity is

`j_n−t_n=Σ_i binom(n,i)b_i V⁽ⁿ⁻ⁱ⁾(0)`.

This preserves the reflected first-atom cancellations. Put `e_i=(16q)^iδ`. The error derivatives obey

`|V⁽ⁿ⁾(0)|≤Σ_i binom(n,i)(|A⁽ⁱ⁾|e_(n−i)+e_i|A⁽ⁿ⁻ⁱ⁾|+e_i e_(n−i))`.

Consequently each of the five signed normalized inputs through order ten has a complete, explicit finite error bound obtained by convolving this expression with `|b_i|` and dividing by `φ²q^k`. Both unequal-source cross terms and the quadratic omitted tail remain present. None of these statements replaces the infinite source by a finite model.

## Exact polynomial model of the retained atoms

The derivative polynomials already used for the first atom satisfy

`P₀(q)=4q²−6q`,

`P_(n+1)(q)=P_n(q)/2+2qP_n′(q)−2qP_n(q)`.

The same recurrence is proved for every literal atom:

`D_x^m thetaCuspSourceTerm(x,n)=exp(x/2−q_n)P_m(q_n)`,

where `q_n=πn² exp(2x)`. In particular `q₂=4q`. Set `z=exp(−3q)` and

`U_n(q,z)=P_n(q)+zP_n(4q)`.

Then `T⁽ⁿ⁾=exp(x/2−q)U_n(q,z)`. Define the finite polynomial

`W_n(q,z)=Σ_i binom(n,i)(−1)^(n−i)U_i(q,z)U_(n−i)(q,z)`.

The exact retained normalized Hankel input is

`(−1)^k t_(2k)/(φ²q^k)=(−1)^k W_(2k)(q,z)/(P₀(q)²q^k)`.

This is an identity at the actual source parameters. A determinant sign certificate for these polynomials and its transfer through the complete error bounds remain to be proved.

## Full mass and slope control

For `q≥37/10`, the second-atom first moment is at most `80 exp(−3q)≤80/50000`. Indeed its rational profile is `48+54/B+18/B²≤80` for `B≥2`; the exponential bound follows from `exp(1)≥27/10` and monotonicity. The deep first moment is at most `8δ≤8/1000000`. Therefore the complete higher-likelihood first moment satisfies

`M₁≤1/500`.

The support bound gives `0≤M₀≤M₁`. Thus

`φ≤Φ≤(101/100)φ`.

The exact full slope is

`Φ′=φ′(1+M₀)−2qφM₁`.

The first-atom polynomial gives `φ′≥(9/2−2q)φ` and, when `q≤5`, `φ′≥−(19/4)φ`. The complete moment bound transports these to

`Φ′≥−5Φ` on `37/10≤q≤5`,

`Φ′≥(4−2q)Φ` on `37/10≤q≤7`.

## Compensation bounds

Let `G=3Φ²+2xΦΦ′`. The quadratic exponential lower bound proves `q≤5 ⇒ x≤1/4`. Consequently

`G≥Φ²/2>0` on `37/10≤q≤5`.

On the whole middle scale interval, the previously proved `16x≤q` and the affine full-source slope bound give

`G≥(3+q/2−q²/4)Φ²`.

The exact nonnegative identity

`q⁵+2592(3+q/2−q²/4)=(q−6)²(q³+12q²+108q+216)`

implies `G≥−q⁵Φ²/2592`. Combining this with the full mass bound proves

`G/(φ²q⁵)≥−1/2500` for `37/10≤q≤7`.

The remaining determinant proof can therefore use nonnegative compensation below scale five and this uniform adverse bound above it. The sign of `H+K_*ΔG` over the middle interval is still open.

## Lean and audit

Eight modules under `formal/GaloisForLFunctions/RHTower` contain 1,152 lines:

- `ThetaCuspDeepTailCalibration`
- `ThetaCuspDeepTailCooling`
- `ThetaCuspTwoAtomSourceApproximation`
- `ThetaCuspTwoAtomReflectedApproximation`
- `ThetaCuspTwoAtomReflectedBounds`
- `ThetaCuspTwoAtomScalePolynomials`
- `ThetaCuspMiddleLikelihoodBounds`
- `ThetaCuspMiddleCompensationBounds`

Each was checked in a scratch tree with `lake env lean`, one foreground process at a time. Only the required new oleans were produced; identical checked source bytes were copied into the corpus. All eight modules are imported by `RHTower.lean`; no umbrella was built. The ten new capstones audited with `#print axioms` depend only on `propext`, `Classical.choice`, and `Quot.sound`, with no added axioms or proof placeholders. The formal lint gate passes.
