# LI local-Bernstein radial-shape no-go

- Killed chain: local all-order Bernstein shape of exact radial response → positive adjacent-current coefficients → paired Li positivity → RH.
- Exact packet: seven nodes with squared value `1/2`, plus conjugate squared nodes `3/4±i`.
- Its real radial response is strictly Bernstein to every order on `0≤v≤1/4`, but completed-Abel endpoint mode `n=3` is negative.
- Positive survivor: coefficient orientation needs global singularity-support control (complete-Bernstein/Stieltjes analytic continuation or support exhaustion); the full local derivative jet cannot exclude farther off-axis poles.
- Formalized closed/unconditionally in `formal/GaloisForLFunctions/RHTower/LiEvenCrossLocalBernsteinShapeNoGo.lean`; umbrella import added to `formal/GaloisForLFunctions/RHTower.lean`.
- Capstones use only `propext`, `Classical.choice`, `Quot.sound`. Direct Lean check and targeted module build pass.
- Card: `docs/drafts/pipeline/3-formalized/li-local-bernstein-radial-shape-no-go.md`. Novelty remains `[NOVELTY UNVERIFIED]` after bounded audit.