# Finite-rank cutoff Ward transgression law

- **ID:** finite-rank-cutoff-ward-transgression
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Internal synthesis of the pointed Fisher cutoff Ward trace and finite-rank trace cyclicity
- **Statement:** Every finite-rank source packet pairs canonically with an arbitrary bounded cutoff edge, and the pairing is exactly the packet evaluation of the adjoint double-commutator curvature.

## Goal

Replace the rank-two-only pointed Fisher trace algebra by one finite-packet law.  The theorem must
retain signed source orientation, permit noncompact bounded channels, expose the exact value relation,
and make complement and involutive reflection available without self-adjointness, idempotence, or
Hilbert--Schmidt hypotheses on the cutoff or channel.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `finiteRankCutoffWardTrace_eq_adjointCurvature_values`, targeted build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Statement

Let `H` be a complex Hilbert space, let `I` be finite, and let

`P = Σ_i c_i |x_i⟩⟨y_i|`

be a finite-rank source packet.  For arbitrary bounded operators `e,T`, put

`K = [T,e] = Te-eT`, `D = [K,e†] = Ke†-e†K`,

and define

`W_e(T;P) = Tr([P,e]† [T,e])`.

Then, unconditionally,

1. `W_e(T;P) = Tr(P† D) = Σ_i conj(c_i) ⟨x_i, D y_i⟩`;
2. the value is conjugate-linear in the packet coefficients and linear in `T`;
3. `W_(1-e)(T;P) = W_e(T;P)`;
4. if `J†=J` and `J²=1`, then simultaneous conjugation preserves the value:
   `W_(JeJ)(JTJ; Σ_i c_i |Jx_i⟩⟨Jy_i|) = W_e(T;P)`;
5. if `e†=e`, then `D=[[T,e],e]`.
6. for two finite packets, the polarized form
   `B_e(P,Q)=Tr([P,e]†[Q,e])` is Hermitian positive semidefinite:
   `B_e(P,Q)=conj(B_e(Q,P))`,
   `B_e(P,P)=‖[P,e]‖_HS²`, and
   `|B_e(P,Q)|≤‖[P,e]‖_HS‖[Q,e]‖_HS`.

The pointed Fisher connection is the `I = Fin 2` packet with the two terms
`2^(-1/2)|χ⟩⟨ψ|` and `2^(-1/2)|ψ⟩⟨χ|`, so all existing pointed value,
channel-splitting, complement, and reflection laws are special cases.  On the diagonal this gives
the exact missing bridge
`W_e(F_{ψ,χ};ψ,χ)=‖[F_{ψ,χ},e]‖_HS²`, so the established complex Fisher phase-defect
formula is also an explicit signed Ward-trace value.

## Proof

`[PROVED HERE]`

Because `P` has finite rank, every product with one factor `P` or `P†` has a summable canonical
diagonal; hence every trace below is defined even when neither `e` nor `T` is compact or
Hilbert--Schmidt.  Taking adjoints gives

`[P,e]† = e†P† - P†e†`.

With `K=[T,e]`, expand the defining trace:

`W_e(T;P) = Tr(e†P†K) - Tr(P†e†K)`.

Finite-rank cyclicity moves the first bounded factor across `P†`:

`Tr(e†P†K) = Tr(P†Ke†)`.

Therefore

`W_e(T;P) = Tr(P†(Ke†-e†K)) = Tr(P†D)`.

Now `P† = Σ_i conj(c_i)|y_i⟩⟨x_i|`, and the rank-one trace identity
`Tr(|y⟩⟨x|D)=⟨x,Dy⟩` yields the displayed finite sum.  Conjugate-linearity in `c` and
linearity in `T` follow directly from that value formula.  Replacing `e` by `1-e` negates both
commutators in the defining pairing, so their product is unchanged.  Under `J†=J` and `J²=1`,
commutators and adjoint curvature transform by `A ↦ JAJ`; the matrix-element identity
`⟨Jx,(JDJ)Jy⟩=⟨x,Dy⟩` proves covariance term by term.  Finally `e†=e` identifies the
adjoint curvature with the ordinary double commutator.

When the channel is a second finite packet `Q`, both cutoff commutators are Hilbert--Schmidt and
the defining trace is exactly their Hilbert--Schmidt inner product.  Conjugate symmetry gives the
packet-exchange reflection, the diagonal inner product is the squared Hilbert--Schmidt norm, and
Cauchy--Schwarz gives the displayed bound.  Thus the signed value law is the polarization of the
existing quadratic cutoff energy rather than a separate scalar construction.

No positivity, RH, source-carrier, compactness, cutoff projection, or channel self-adjointness
assumption is used.

## Hostile audit and novelty

- Trace cyclicity with one finite-rank/trace-class factor is classical operator theory.  Burnol's
  conductor work supplies the arithmetic operator context and studies the conductor and its
  commutators, but does not state this finite-packet polarized cutoff identity:
  [Burnol, *The Explicit Formula and the conductor operator*](https://arxiv.org/abs/math/9902080) and
  [Burnol, *Spectral Analysis of the local Commutator Operators*](https://arxiv.org/abs/math/9812012).
- The theorem is therefore classified as **not new standalone scientific knowledge**.  Its genuine
  contribution is structural and formal: it removes the accidental rank-two restriction, exposes
  the complete source conjugate-linearity interface, and turns every finite arithmetic source
  packet into a legal value probe for a bounded noncompact Burnol edge.
- It does **not** construct the missing prime--Gamma-to-Sonin carrier, prove positivity, or advance
  RH by itself.  Those claims are explicitly excluded.

## Lean surface

- General packet, sandwich, adjoint, summable trace diagonal, value law, and finite-rank cyclicity:
  `GaloisForLFunctions.HTGeometry.FiniteRankCutoffWardTrace`.
- Exact transgression and value interfaces:
  `finiteRankCutoffWardTrace_eq_opTrace_adjointCurvature`,
  `finiteRankCutoffWardTrace_eq_adjointCurvature_values`, and
  `finiteRankCutoffWardTrace_eq_curvature_values`.
- Discharged interfaces: `finiteRankCutoffWardTrace_add_coeff`,
  `finiteRankCutoffWardTrace_smul_coeff`, `finiteRankCutoffWardTrace_add_channel`,
  `finiteRankCutoffWardTrace_one_sub`, and
  `finiteRankCutoffWardTrace_conjugate_involution`.
- Hermitian energy polarization: `finiteRankCutoffWardForm_eq_hsInner`,
  `finiteRankCutoffWardForm_conj_symm`,
  `finiteRankCutoffWardForm_self_eq_hsNormSq`,
  `finiteRankCutoffWardForm_self_re_nonneg`, and
  `norm_finiteRankCutoffWardForm_le`.
- Literal rank-two subsumption:
  `finiteRankCutoffWardTrace_finTwo_eq_pointedCutoffWardTrace`,
  `pointedCutoffWardTrace_self_eq_hsNormSq`, and
  `pointedCutoffWardTrace_self_eq_phase`.
- Burnol reflection, Lüders discharge/split, and concrete even-Sonin packet laws:
  `GaloisForLFunctions.RHTower.SoninBurnolFiniteRankWardTrace`.

## Log

- 2026-07-19 — corpus audit found no generic finite-rank packet law; paper theorem proved and placed in Stage 2.
- 2026-07-19 — formalized the general law and its Sonin--Burnol specialization; exact targeted build and axiom audit passed; promoted to Stage 3.
- 2026-07-19 — connected the signed value theory to the quadratic cutoff theory by formalizing the Hermitian finite-packet Ward polarization and its exact diagonal energy law.
- 2026-07-19 — closed the pointed API gap: the diagonal signed Fisher Ward trace now rewrites directly to the full complex phase-sensitive cutoff energy.
