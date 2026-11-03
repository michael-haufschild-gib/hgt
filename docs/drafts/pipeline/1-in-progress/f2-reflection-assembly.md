# F2 — reflection assembly

- **Stage:** 1-in-progress
- **Goal:** Realize the arithmetic Hecke action on complete Weil energy through PM periods and WTZ correspondences; prove the missing positivity.
- **Open:** Complete Weil positivity / PM Krein positivity. No sign assumption is admitted.

## Established bridges

**Reflection centralizer [K].** On all functions supported in `[−A,0]`, `ρ_A(f)` commutes with Serre reflection iff all active coefficients `f(n)`, `n≥2`, vanish. On smooth window tests the exact condition is `f(n)=0` for `log n<A`; full-length shifts annihilate continuous tests. Thus the commuting action is scalar. Non-scalar Hecke transport must use adjoints, larger stages, or cusp channels. [Proof and declarations](../3-formalized/f2-window-reflection-centralizer.md).

**Barnes Hecke identity [K].** For `P_w(a,b)=ζ₂(a|a,b;w)+ζ₂(b|a,b;w)`, positive `a,b`, `Re w>2`,

`P_w(2a,b)+P_w(a,2b)+P_w(a+b,2b)+P_w(2a,a+b)=P_w(a,b)+2P_w(2a,2b)`.

Mellin integration of the exact rational kernel identity and cone homogeneity give the actual four-branch eigenvalue `1+2·2^(−w)`. [Proof and declarations](../3-formalized/f2-barnes-hecke-source-identity.md).

**Source inputs.** `FareyLewisTransferAndCuspSeparation` supplies Hecke/inversion commutation and Farey-defect transport; its dependency build has standard-only axioms. `MayerWindowFoldTransfer` supplies logarithmic integral-pairing transport, explicit negative Frobenius-square defect, and fold bounds; its formalized card records the individual Lean audit.

## Cusp admission [K]

If `f=0` above `R≥0`, then for `a>2R`,

`(a+1)^(2s) T₂f(a)=f(2a/(a+1))`.

The Möbius map bijects an upper tail with a left germ at `2`; inverse `x/(2−x)`. Hence the output has a finite upper cutoff iff the input vanishes on that germ. For `f=windowPeriodLift s H`, this is exactly the right germ of `H` at `−log2`. Inversion then ties upper and lower tails.

Every smooth stage-`A` test has finite Hecke support iff **`A<log2`**. For `A>log2`, a bump nonzero at `−log2` obstructs cutoff. At equality, a smooth function with nonzero set exactly `(−log2,0)` has zero endpoint value but a nonzero germ. This is the positive survivor of the failed finite-window-endomorphism conjecture: an exact admission classification and recovered cusp channel.

[Proof and declarations](../3-formalized/f2-sharp-hecke-cusp-admission.md); [failed universal finite-window claim](../5-failed/f2-finite-window-hecke-stability.md).

## Completed periods and finite-energy cores

**Completed-period eigenvalue [K].** Write `E_s` for the actual Eisenstein Lewis period. The Barnes identity, pole-cleared parameter continuation, and real-analytic continuation in `a>0` give

`T₂,s E_s=(1+2·2^(−2s))E_s`, `0<Re s<1/2`.

Also `E_s(1)=2ζ(2s−1)≠0` throughout this strip. At resonances `E_s` is the actual resonant Lewis period. [Proof and declarations](../3-formalized/f2-global-lewis-hecke-eigenvalue.md).

**Core correction [K].** PM's Krein basis uses `mayerPeriodCore`, subtracting both zeta-axis and scattering-power terms. With `q=2^(−2s)` and `c=2ζ(2s−1)/(2s−1)`,

`T₂(core_s)(1)−(1+2q)core_s(1)=−2qζ(2s)+c(1−4q)`.

At every upper resonance this is nonzero: `ζ(2s)=0`, `c≠0`, `|4q|>1`. Thus the completed-period eigenvalue is not a diagonal action of the uncorrected Hecke operator on PM's actual core basis, even on the critical line. [Proof and declarations](../3-formalized/f2-hecke-scattering-boundary-correction.md).

## Across-stage Mellin correspondence [K]

Set `L=log2`, `F₂H(u)=√2H(u+L)`, `V₂H(u)=√2H(u)`, and

`Φ_H(s,a)=tr(H)(2s)E_s(a)/E_s(1)`, where `tr(H)(z)=∫H(u)e^((z−1/2)u)du`.

Then:

- `Φ_H(s,1)=tr(H)(2s)`; `(T₂,s−Id)Φ_H=Φ_(F₂H)` on `a>0`.
- Both branches map stage `A` into `A+L`. On supported tests, `F₂=√2·adjointShift(A+L,L)`, with no truncation loss.
- `Q(F₂H)=Q(V₂H)=2Q(H)` for the complete Weil form.
- `σ_(A+L)F₂=V₂σ_A`, `σ_(A+L)V₂=F₂σ_A`. The sum intertwines reflections but retains a mixed Weil term.
- The complete explicit formula becomes
  `Q(H)=Re Σ_ρ m_ρ Φ_H(ρ/2,1) conjugate(Φ_H((1−conjugateρ)/2,1))`.
- Reflection changes parameter:
  `Φ_(σ_AH)(s,1)=exp(−A(2s−1/2)) Φ_H(1/2−s,1)`.

The new content is the actual source Hecke realization of the window translation similitude. These identities do not supply positivity. [Proof and declarations](../3-formalized/f2-hecke-window-mellin-correspondence.md).

## Remaining assembly

**Literal linear reflection identification fails [K].** Every `A>0` admits a smooth `σ_A`-odd unit test with `Q(H)≥1/4`. Every `Θ_PM`-odd vector has Krein square `−⟨v,v⟩⁺≤0`. Hence no real-linear map preserves both forms and intertwines these involutions. The positive survivors are the quantitative odd witness and the exact conjugate-linear, exponentially twisted Mellin reflection; both are Lean-audited. [Obstruction, survivor, declarations](../5-failed/f2-literal-linear-reflection-isometry.md).

`U_LP` transports the integral pairing `lewisCriticalInner`, not PM's coefficient pairing `mayerKreinPosInner`. Every direct window lift is fixed by its own `I_s`; this cannot identify the original nontrivial `σ_A` with `I_s`. PM's linear Krein reflection exchanges `s↔1/2−conjugate(s)`, while window reflection on real Mellin data additionally involves conjugation and an exponential twist.

The signed correspondence below retains the core correction and the conjugation/twist. A compatible positive source realization or arithmetic lower bound remains required.

**Finite-core identification [K].** For a finite set `S` of upper resonances closed under `s↦s♯=1/2−conjugate(s)`, form the actual PM vector
`v_S(H)=Σ_(s∈S) √m_(2s) Φ_H(s,1)b_s`, where `b_s` is the existing core basis. Its Krein square equals the upper-zero Weil partial sum: the basis coordinates pair exactly at `s,s♯`, and reflection preserves multiplicity. Twice its real part converges to `Q(H)`: conjugation bijects the upper and lower zero sets, conjugates each real-test Weil summand, and the existing absolute summability controls the finite sums. Closing finite sets under reflection is cofinal. Window reflection acts on coefficients as `D_A·conjugation·Θ_PM`, where `D_A(s)=exp(−A(2s−1/2))`. The coefficients are the existing CWS `windowZeroMap`; the vectors are finite sums in the existing PM core space. No integral metric or new completion is assumed. The source Hecke multiplier on each coefficient is `2·2^(−2s)`. [Proof and declarations](../3-formalized/f2-weil-form-as-core-packet-limit.md).

**Finite projection and tail compensation [K].** Existing interval interpolation, applied to the distinct nodes `γ_(2s),−conjugate(γ_(2s))` with conjugate data, gives a real test after taking its real part. Translating into `[−A,0]` and dividing by the positive square-root multiplicities prescribes every finite upper-resonance coefficient for any `A>0`. Hence every finite PM core vector in the selected span is a window projection.

A finite projection is nonnegative on all tests iff every included resonance lies on `Re s=1/4`: otherwise realize the existing vector `b_s−b_(s♯)` with Krein square `−2`; on the line reflection fixes the span. For `0<A≤1/1000`, CWS coercivity then forces the omitted tail of this witness to satisfy `Q(H)−2[v_S(H),v_S(H)]_PM ≥ 4+∫H²/4`. Short-window positivity controls the complete sum, not each finite truncation. [Proof and declarations](../3-formalized/f2-finite-core-projection-and-tail-compensation.md).

## Iterated cusp admission

**Second Hecke step [K].** For `A<log(4/3)`, a window lift has a finite second-image upper cutoff iff `H` vanishes on a left germ at `0`. Every `A>0` contains a single smooth test with compact first image and noncompact second image at every complex parameter. The exact admission law follows because only the halving branch survives near the first cusp: `T₂f(x)=2^(−2s)f(x/2)`. [Proof and declarations](../3-formalized/f2-second-hecke-endpoint-admission.md); [failed aperture-only iteration claim](../5-failed/f2-small-window-iterated-hecke-admission.md). Finite-energy cusp completions remain available.

**Stable finite-energy carrier [K].** Despite compact-support failure, every finite ordered word in the actual `T₂,s,T₃,s`, applied to any window lift at any aperture, satisfies `|f(a)|≤C(1+a)^(−2 Re s)`. For `Re s>0` it has finite upper Haar square and dyadic cusp energy. Each positive branch preserves the weighted bound; sums cost factors four or seven. This supplies a stable admission class, while the outgoing wave remains a separate boundary channel. [Proof and declarations](../3-formalized/f2-hecke-cusp-decay-carrier.md).

**Second-prime source action [K].** The seven determinant-three Barnes cones, reciprocal folding into the original Mayer disc, and two analytic continuations give `T₃E_s=(1+3·3^(−2s))E_s` on the whole positive line. The same normalized period now satisfies `(T₃−Id)Φ_H=Φ_(√3 H(·+log3))`, mapping stage `A` into `A+log3` and scaling complete Weil energy by three. Both prime grids therefore act through actual source correspondences. Existing two-prime index recovery applies to their arithmetic multipliers; the sign of the complete orbit form remains open. [Proof and declarations](../3-formalized/f2-second-prime-source-hecke.md).

**Physical-core admission [K].** The actual `mayerPeriodCore s`, for every `0<Re s<1/2`, `Im s>0`, lies in the same weighted decay carrier as the window lifts. The field estimates and the Cauchy kernel's absolute Mellin moments at `0,1` prove the bound on the whole positive line. Every finite mixed source word therefore has finite upper Haar square and dyadic cusp energy, without a resonance assumption. Constants depend on the spectral parameter; [Gaussian physical synthesis](f2-gaussian-physical-core-synthesis.md) addresses the separate infinite-sum question. [Proof and declarations](../3-formalized/f2-physical-core-cusp-carrier.md).

## Completion gates

- [x] Exact Hecke transport and sharp support/cusp law, paper proof and Lean.
- [x] Across-stage WTZ correspondence and complete Weil-form identity, Lean audited.
- [x] Corrected core/signed-form reflection identification.
- [ ] Missing positivity proved without sign or resonance-admission assumptions.
- [ ] Individual final audits, standard-only transitive axioms, umbrella imports.
