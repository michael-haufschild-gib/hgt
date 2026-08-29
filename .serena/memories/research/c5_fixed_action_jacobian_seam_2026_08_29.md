# C5 fixed-action Jacobian seam, 2026-08-29

- Direct C5 fixed-action Jacobian J survives 2D hostile scan and compulsory seam attack. Do not confuse with retired two-sign velocity-current decomposition.
- Exact paper identity at seam: J_u(0,t)=q_t(F_a q_tuu+F_b q_ttuu)-q_uu(F_t+F_a q_tt+F_b q_ttt); all F_q terms cancel.
- Exact symbolic Taylor discovery: first nonzero displacement term is t^5. With A=-L2, B=-L4, C=-L6, D=-L8, numerator is A^2 D -18 A^3 C +36 A^2 B^2 -5 A B C +4 B^3. Existing strict law AC<2B^2 supplies positive block 18 A^2(2B^2-AC), so old no-go helps direct route.
- RunPod 128-worker, 240-dps scan: 633,332/633,332 seam margins positive on 1e-8<=t<=100. 80 dps falsely negative at t=50; 160/240/480 stabilized positive. Diagnostic only, forbidden in Lean.
- Global centre monotonicity of J/u is computationally false: at t=1e-3 ratio to seam falls to .2523 at u=.5, rises to 21.244 at u=2, then tail collapses. Use three-region local/compact/first-atom-tail proof, not a monotone-centre reduction.
- Computation folder: docs/drafts/pipeline/2-fully-proven/computations/2026-08-29-c5-fixed-action-jacobian-seam/.
- Lean module formal/GaloisForLFunctions/RHTower/ThetaCuspFixedActionC5Jacobian.lean now proves action/jet parity, J odd, and algebraic J/u even, with no numeric inputs. Exact module build passed; axioms only propext, Classical.choice, Quot.sound. Wired into RHTower umbrella.
- Cards/frontier map updated. New paper target: exact modular-ODE certificate for eighth-order seam polynomial, then analytic positivity of scalar seam M(t), compact middle J/u, and first-atom tail.