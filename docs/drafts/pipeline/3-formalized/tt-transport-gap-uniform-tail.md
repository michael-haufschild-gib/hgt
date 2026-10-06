# Uniform direction tail for the actual fourth Schur gap

- **ID:** tt-transport-gap-uniform-tail
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route TT; `ThetaCuspNativeOddFourCofinal`, `ThetaCuspNativeTwelfthJetLimit`, `ThetaCuspCoupledOddTransportSchur`.
- **Statement:** For every fixed real load C, there is R>0 such that every x≥R and every real t satisfy `schurGap C x t>0`. The actual residual-free transported fourth determinant is eventually strictly positive.

## Goal

Close the tail sign for the literal transported fourth gap without a bound on
the direction or its growth. Compact gap positivity, decay of the correction
flux, a compatible join and all-rank closure remain open. This is not RH.

## Gates

- [x] Source-pure statement and corpus audit.
- [x] Complete dependency-closed paper proof, proved here.
- [x] Direct Lean leaf audits and imported axiom audit.
- [ ] Publication-ready standalone presentation.

## Proof

Let N(x) be the complete native odd-four matrix and G(x) the actual center
compensation source. Set L(C,x)=N(x)+C G(x)e₃e₃ᵀ. The existing Gaussian
balancing is N=q Dᵀ Nscaled D, with Dᵢᵢ=f qⁱ, where q is the first-atom
reflection scale and f its source term. The additional balanced last entry is
C G/(f²q⁷). Its limit is zero: the proved limit G/(f²q⁶)→0 multiplied by
q⁻¹→0. Every balanced native entry tends to the positive definite Gaussian
odd-four matrix. Positive definiteness is open, so for each fixed C the entire
loaded matrix L(C,x) is positive definite beyond one center R.

For arbitrary t, take the three independent columns e₀,e₁,e₃−t e₂. Their
matrix E(t) is injective for every t. Hence E(t)ᵀL(C,x)E(t) is positive
definite, with a strictly positive determinant, at every x≥R. Expanding this
three-by-three determinant gives exactly

`A(x)+C G(x)H(x)+2 B(x)t+D₃(x)t² = schurGap C x t`.

Here A and B are the complete source cofactors and H the native odd head.
No moment, source tail or direction term has been omitted. Crucially R was
chosen before t, so the tail is uniform over all real directions.

Apply the result at the actual `direction x`. Its exact transport law makes
the squared Schur residual zero. The already proved positive native head and
canonical compensated third determinant then imply strict positivity of the
complete transported fourth determinant. No derivative-sign premise or bound
on `direction` enters the proof.

## Audit log

- 2026-10-06 — Corpus deep searches inspected with partial/freshness metadata;
  exact supporting source files read. Scratch files
  `/tmp/TTC91OddDiagonalTail.lean`, `/tmp/TTC91TransportGapTail.lean` prepared.
  Sole foreground driver16463 is auditing them serially. Lean status pending.
- Scope boundary: eventual gap positivity does not establish correction-flux
  integrability or a source-compatible join. No bounded-center claim is made.
- 2026-10-06 — Both scratch leaves passed; two production leaves
  `ThetaCuspOddFourDiagonalTail` and `ThetaCuspOddTransportGapTail` passed direct
  `lake --old env lean -o ... <module>` audits and are wired into `RHTower`.
  Seven imported capstones passed with only `propext`, `Classical.choice`,
  `Quot.sound`. Main result `eventually_all_schurGap_pos`; actual transport
  result `eventually_transported_determinant_pos`. No umbrella build.
  Audit driver81505 then continued to C88 control14.
- Formal lint50423 exited1 only for unrelated unreachable modules
  `KuznetsovKernelOscillatory` and `KuznetsovSqrtSeparation`. New TT leaves have
  no lint errors; the global lint gate is not green.
