# Original arithmetic kernel and cross-frequency Wronskian

- Stage: 1-in-progress
- Parent: [Selberg conjecturing loop](selberg-quarter-conjecturing-loop.md), cycle54.
- Objective: recover the complete arithmetic mixed Gram form, then derive actual cross-frequency transport and a positive integral kernel for the original Maass Fourier coefficients.

## Corpus evidence and conjecturing loop

Explicit-OR Gram/Fourier/annihilator/Kloosterman discovery found14539 metadata declarations in2983 modules;10000 were retrieved in `/tmp/selberg_kernel56_corpus.json`. A second page retrieved4544 records after the concurrently maintained index grew to14544 matches; this is paginated discovery, not a frozen-dataset coverage claim. Explicit-OR Bessel/Loewner/Dirichlet-to-Neumann/divided-difference/Wronskian discovery retrieved all3579 metadata matches in670 modules in `/tmp/selberg_kernel56_boundary.json`. Counts describe discovery metadata, not proof-body coverage. Inspected the actual complete-column additive-character cancellation proof, original annihilator-fibre and convolution proofs, actual projector adjoint/orthogonality proofs, source coefficient derivatives/modal equation, and Dunster's weighted-Wronskian potential-defect cancellation proof.

Conjecture1: the full complex mixed transfer form is `inner(v,Gw)`, with `G=P_s Q_(-r) P_s`. Thus the original real loss has its exact complex convolution expression, with first-slot conjugation and every composite-level fibre phase retained. Distinct original Fourier residue channels should cancel exactly.

Conjecture2, prompted by the corpus Wronskian proof: for original coefficient vectors `c_n(y)` and `c_m(y)`, the Wronskian built from the fixed arithmetic loss form has derivative `(k_n²-k_m²) B(c_n,c_m)`. The common potential `lambda/y²` cancels. Integrating should retain the actual endpoint currents, while the mixed integral is a positive Gram kernel on every finite family. This targets the surviving same-residue interference in the horizontally weighted top boundary term; no sign for that top boundary, spectral estimate, or assumed lift is supplied.

## Paper proof

Move the actual self-adjoint projectors across the Hermitian inner product and apply the original inversion-unitary conjugation to obtain the full mixed Gram equality. Substitute the already constructed convolution kernel. The exact original coefficient eigenspaces give residue orthogonality.

Differentiate `B(c_n',c_m)-B(c_n,c_m')`. The two first-derivative cross terms cancel. Substitute the actual coefficient ODE `c_n''=(k_n²-lambda/y²)c_n`; shared potential cancellation leaves the asserted frequency difference. Continuity comes from the actual first and second coefficient derivatives, so finite-interval FTC requires no new analytical premise. Positive integral quadratic forms follow by finite sesquilinear expansion of the already proved nonnegative original transfer loss.

## Endpoint and quantitative conjectures proved

The original coefficient and derivative square integrals are finite on every positive cusp tail. Finite deck summation proves this for the full vectors. The actual contraction bounds the complex loss by the sum of the two squared norms, so both the Wronskian and its actual derivative are integrable. The corpus improper-integral theorem therefore proves the current tends to zero at infinity. No endpoint is assumed.

Write `H_nm(Y)=integral_(Y,infinity) B(c_n,c_m)`. The exact boundary law is

`W_nm(Y)=(k_m²-k_n²) H_nm(Y)`.

The complete kernel is Hermitian; distinct residues have zero entries. Every finite complex superposition satisfies

`sum_nm conjugate(a_n)*a_m*H_nm = integral_(Y,infinity) lossEnergy(sum_n a_n*c_n)`.

Its real part is nonnegative. This identity preserves actual phases; no absolute-kernel substitution is made. Testing the two-mode quadratic with coefficient `t*conjugate(H_nm)` and using the corpus discriminant lemma proves

`norm(H_nm)² <= Re(H_nn)*Re(H_mm)`.

Consequently

`norm(W_nm(Y))² <= (k_m²-k_n²)² * Re(H_nn(Y))*Re(H_mm(Y))`.

All diagonal and zero-loss cases are included. Opposite signed indices have exactly zero Wronskian, since their squared frequencies coincide. This is a quantitative bound on the original arithmetic mixed boundary current, not a sign assumption on the full top boundary stress.

Source: [SelbergMaassKernelWronskian](../../../../../../formal/GaloisForLFunctions/RHTower/SelbergMaassKernelWronskian.lean),414 lines,30 public declarations.

## Verification

- [x] Complete scratch proofs with `lake env lean`.
- [x] Exact source check and one final targeted module build.
- [x] All30 public declarations passed the standard-axiom audit; source hash unchanged.
- [x] Exact-module search and generated API cover all30 public declarations; one umbrella import.
- [x] Repository formal lint passed; all task-owned handles terminal and no remaining owned worker; source hashes unchanged.

The final single-module `lake build GaloisForLFunctions.RHTower.SelbergMaassKernelWronskian` rebuilt only that module in5.8s. Scratch/source checks are clean. All30 declarations use only `propext`, `Classical.choice`, and `Quot.sound`; no added axiom or admission. Checks and builds were strictly serial foreground Lean invocations. Artifacts use `/tmp/selberg_kernel56_`.

The final source SHA256 agrees with the manifest. Exact-module research and API checks cover every public declaration. Index refresh and repository formal lint passed. Local links and task-file whitespace checks passed; the previous PhaseStress source hash is unchanged. No full or umbrella build, numerical experiment, commit, or push. Audit certificate: `/tmp/selberg_kernel56_audit.json`.

## Next positive comparison

The proposed reconstruction-first continuation was paused after a user-triggered [duplication audit](selberg-weighted-top-fourier.md). Actual source absolute summability, complete derivative Parseval, and core–cusp gluing already exist. The checked new Wronskian/tail identities have not yet yielded a stronger all-level spectral comparison. Before adding another module, establish on paper a direct estimate for the complete existing core–cusp quarter form using the actual arithmetic constraints. Do not assign a sign to frequency reweighting merely because the underlying tail kernel is positive, or count another equivalent boundary representation as closure of that estimate.

The full Selberg1/4 theorem remains active and unproved. This card records intermediate positive mathematics, not completion of the root goal.
