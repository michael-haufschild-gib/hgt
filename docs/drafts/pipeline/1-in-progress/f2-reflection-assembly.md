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

**Unique core boundary charge [K].** At every upper resonance, with `w=2s`, the lower trace of `T₂ core_s` is `core_s(2)=ζ(w−1)(w−2−4·2^(−w))/(w−1)≠0`. Hence the raw Hecke image leaves whole-Haar `L²`, even on the critical line. Subtracting `d·1_(0,1)` restores finite energy exactly when `d=core_s(2)`. This retains the boundary coordinate uniquely; it supplies no sign criterion. [Proof and declarations](../3-formalized/f2-core-hecke-boundary-charge.md).

**Global actual-core identity [K].** For every upper-strip parameter, the literal Cauchy core is real analytic on `(0,∞)` and satisfies `core_s=E_s−ζ(2s)(1+a^(−2s))−2ζ(2s−1)/(2s−1)·scatteringPowers(2s,a)` there. Removing one explicit field trace supplies an exponentially decaying logarithmic source; its Cauchy average and the retained step primitive give pointwise analyticity. [Proof and declarations](../3-formalized/f2-global-actual-core-identity.md).

**Corrected all-prime core transport [K].** The values at `1,2` recover both boundary coefficients through the nonzero determinant `1−(2s+1)2^(−2s)`. Adding their exact source-Hecke errors gives `T̂_(p,s)core_s=(1+p^(1−2s))core_s` for every prime and every upper-strip parameter. At resonances the zeta-axis channel vanishes; the scattering coefficient is `core_s(1)/(2s−3)`. This realizes the arithmetic eigenlaw on actual cores while retaining their boundary correction. [Proof and declarations](../3-formalized/f2-global-core-hecke-correction.md).

**Retained-boundary source carrier [K].** Restoration loses exactly the zeta-axis direction; retaining its evaluation coordinate gives unique reconstruction. Inversion and the Lewis three-term equation force the first-prime boundary eigenvalue and carrier invariance. Corrected `T₂` intertwines with the actual source operator on this whole carrier, which contains every upper-strip core. [Proof and declarations](../3-formalized/f2-boundary-restoration-carrier.md). Signed-form descent remains open.

**Complete source-carrier invariance [K].** Every positive-determinant source Hecke operator preserves the full inversion-fixed, three-term Lewis carrier, for every complex parameter. Unique matrix normal forms give a finite suffix partition; harmonic summation transports the three-term equation, while basis reversal transports inversion. [Proof and declarations](../3-formalized/f2-all-determinant-lewis-carrier.md). For every prime, the three-term equation alone also gives `Tₚg(1)=(1+p^(1−2s))g(1)`, without inversion or a strip restriction. Primitive row sums form a finite suffix partition; the remaining `p` bases have equal row sums `(p,p)`.

**All-prime retained-boundary transport [K].** On `0<Re s<1/2`, reconstruction `F(g,c)=g−c(1+a^(−2s))−g(1)/(2s−1)·scatteringPowers(2s,a)` satisfies `T̂ₚF(g,c)=F(Tₚg,(1+p^(1−2s))c)` on the full completed Lewis carrier. Thus every corrected prime correspondence preserves the physical boundary extension and intertwines its restoration. [Proof and declarations](../3-formalized/f2-all-prime-lewis-carrier.md). A common bounded action on mixed-parameter physical sums and positive signed-form descent remain open.

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

**Physical-core admission [K].** The actual `mayerPeriodCore s`, for every `0<Re s<1/2`, `Im s>0`, lies in the same weighted decay carrier as the window lifts. The field estimates and the Cauchy kernel's absolute Mellin moments at `0,1` prove the bound on the whole positive line. Every finite mixed source word therefore has finite upper Haar square and dyadic cusp energy, without a resonance assumption. Constants depend on the spectral parameter; [Gaussian physical synthesis](../3-formalized/f2-gaussian-physical-core-synthesis.md) addresses the separate infinite-sum question. [Proof and declarations](../3-formalized/f2-physical-core-cusp-carrier.md).

**Uniform spectral control [K].** Exact theta correlation and Cauchy normalization now give `|core_s(a)|≤C(1+Im s)^N exp(π Im s/2)a^(−Re s)` for every upper resonance. The zero-free region controls the reciprocal strip distance, with no exceptional height range. This supplies the spectral estimate used in Gaussian synthesis of the actual core sums. [Proof and declarations](../3-formalized/f2-uniform-physical-core-spectral-bound.md).

**Gaussian physical synthesis [K].** For every positive damping parameter and every existing CWS zero-space vector, the actual core series converges absolutely at each positive physical coordinate and in upper Haar `L²`. The same damping respects reflected coefficient products, and the damped Weil energy tends to the complete form as damping vanishes. This supplies a physical infinite sum; its Haar norm is not identified with the signed pairing. [Proof and declarations](../3-formalized/f2-gaussian-physical-core-synthesis.md). [Upper-coordinate faithfulness](../3-formalized/f2-faithful-gaussian-core-completion.md) is now audited, including Haar-almost-everywhere uniqueness.

**Both physical endpoints [K].** The zero theta-Mellin mass now yields `|core_s(a)|≤K(s)min(a⁻¹,a^(1−2 Re s))` with a uniform polynomial-exponential spectral factor. The Cauchy first moment preserves outgoing decay, and modular inversion supplies the endpoint at zero. This sharpens the estimate needed for whole-line Haar synthesis and common-strip Mellin interchange. [Proof and declarations](../3-formalized/f2-resonant-core-two-endpoint-bound.md).

**Whole-axis Mellin bridge [K].** Gaussian core synthesis now converges in `L²((0,∞),da/a)`, and its literal Mellin transform on `0<Re u<1` equals the sum of the individual transforms. Each core transform is holomorphic on `2 Re s−1<Re u<1`. The endpoint estimate, reflected zero-free bound and absolute integral summability prove these statements. [Proof and declarations](../3-formalized/f2-whole-axis-gaussian-mellin-synthesis.md). [Normal continuation and nonzero residue extraction](../3-formalized/f2-faithful-gaussian-core-completion.md) prove that this whole-axis synthesis vanishes iff every upper-resonance coefficient vanishes. Lower coordinates are absent; no bounded inverse or positive metric identification follows. A [universal physical antiunitary](../3-formalized/f2-arithmetic-mellin-reflection.md) now exchanges the Gamma-normalized resonant theta fields in logarithmic Haar `L²` [K]. The literal core Mellin reflection retains its extra Cauchy multiplier. Its [sharp norm and domain classification](../3-formalized/f2-cauchy-reflection-order.md) is audited [K]: exact order `1/2−2 Re s`, bounded realization iff `Re s≥1/4`, both directions bounded iff `Re s=1/4`. [Actual averaging forces this correction](../3-formalized/f2-cauchy-compatible-reflection.md), with no multiplier assumption on the candidate [K]. The compatible bounded conjugate-linear reflection is unique, exchanges actual core columns, and is antiunitary on the critical line. [Local source-window determination](../3-formalized/f2-local-cauchy-range-density.md) is now audited [K]: every nonempty interval has dense Cauchy range, and compatibility there forces the same global reflection and sharp boundary. These inputs are unrestricted interval sources; the paired WTZ period lift remains distinct. A [canonical closed full-strip reflection](../3-formalized/f2-closed-cauchy-reflection.md) is now audited [K]: its domain is dense, reflected parameters give inverse graphs, and actual PM cores are exchanged. Every nonempty source interval generates the same minimal closed graph. [Whole-Haar admission of the actual paired WTZ Hecke image](../3-formalized/f2-whole-haar-hecke-admission.md) is audited [K]: finite energy iff `H(−log2)=0`, universal admission iff `A≤log2`. At equality finite Haar energy can coexist with noncompact support. Signed-form positivity remains open.

## Completion gates

- [x] Exact Hecke transport and sharp support/cusp law, paper proof and Lean.
- [x] Across-stage WTZ correspondence and complete Weil-form identity, Lean audited.
- [x] Corrected core/signed-form reflection identification.
- [ ] Missing positivity proved without sign or resonance-admission assumptions.
- [ ] Individual final audits, standard-only transitive axioms, umbrella imports.
