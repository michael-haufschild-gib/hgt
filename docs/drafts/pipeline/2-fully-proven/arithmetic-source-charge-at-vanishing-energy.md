# Arithmetic source charge at vanishing energy

- **ID:** critical-rigidity-vanishing-energy-charge
- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Lean:** `CriticalScaleArithmeticRigidity/VanishingEnergyCharge.lean` — pending check

## Statement

For every real charge `t`, positive tolerance `ε`, and lower conductor cutoff `R`, there is `Q≥max(R,2)` such that every finite horizon `N≥1` admits an actual harmonic-pole-neutral packet `a` satisfying

`L_Q(a)<ε`, `mean G_Q(a)=t`, and `mean |G_Q(a)−t|²<ε`.

Here `G` is the literal complete Mangoldt-weighted dilation generator, and the means are complete-period means. No conclusion about the sign of the complete Weil form is included.

## Proof

Put `B_Q=Σ_(p≤Q)log p/p` and `w_p=sqrt(p−1)/p`. On prime-supported coefficients, `P_Q(w)=L_Q(w)=B_Q`. The exact generator decomposition is

`G_Q(a)=P_Q(a)−Σ_p tameDifferent(p)a_p e_p`,

and its centered square is at most `k L_Q(a)`, where `k=log 2/2` is sharp. For `a=(t/B_Q)w`, the charge is exactly `t` and the energy is `t²/B_Q`. The prime Mertens theorem gives `B_Q→∞`; choose `Q≥max(R,2)` with `(1+k)t²/B_Q<ε`. Both the input energy and the centered output square are then less than `ε`.

The actual harmonic projection changes only coefficient one. It leaves both `L_Q` and `G_Q` unchanged and imposes the literal horizon pole constraint. This works for every `N≥1` at the same chosen conductor cutoff.

## Insight and positive survivor

Adjunction-energy convergence alone loses a freely prescribed constant receiving charge, even under physical input pole neutrality. On prime input, output modulo constants remains bounded with exact squared norm `log 2/2`. A source-preserving limit must retain charge as separate data or obtain its cancellation from the complete signed form.

This proves an explicit concentration family. An infinite-dimensional graph-closure classification and nonconstant receiving charges remain separate questions.
