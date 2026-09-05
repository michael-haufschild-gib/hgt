# Prime/integer energy separation (2026-09-05)

New leaf: formal/GaloisForLFunctions/RHTower/GibbsPrimeIntegerFootprint.lean (384 lines), wired into RHTower.lean. Namespace RHTower.

Closed Lean results:
- fullEuler_weighted_energy_div_rpow_tendsto: full prime product energy on [-1,1], with any continuous nonnegative weight positive at zero, divided by Y^b tends to infinity for every real b and 0<a<=1/2 (sigma=1-a).
- fullEuler_integer_section_residual_ratio_one: subtracting any fixed bounded-coefficient integer Mellin section of length floor(Y)^k leaves relative energy tending to one, for every natural k and 1/2<=sigma<1.
- fullPrimeEulerGamma_mobius_section_residual_ratio_one: unconditional specialization to literal Gamma weight and literal Moebius coefficients.

Scope: prime aperture differs from integer height. For k=1, integer prefix matches low-degree part of full Euler expansion. For k>1, a full integer prefix can include primes above Y, so this is an additive correction, NOT automatically a literal prime-product tail. These theorems neither bound nor disprove bounded literal Moebius-prefix Gamma--Hankel returns. They rule out polynomial-length additive repairs of the full-prime approximation.

Validation: lake env lean /tmp/hgt_prime_integer_footprint.lean exited 0; three capstone #print axioms only propext/Classical.choice/Quot.sound. Installed body checked byte-equal to scratch (excluding header/axiom commands). formal_tools.py lint passed (existing large-file warnings); git diff --check passed. No full/umbrella builds. Only missing GibbsFullPrimeGammaEscape.olean was built via lake env lean -o. All owned Lean sessions finished.

STATUS F652 strengthened; F654 added. STATUS had 4999 lines. Other agents concurrently own changes including final Riemann-Siegel section with duplicate IDs; preserved.

Solved-analogue audit: Huijse-Schoutens arXiv:0903.0784 classifies SUSY lattice ground states via rhombus tilings; Witten index alone does not bound unsigned ground-state count. Bjorner arXiv:1101.5704 already realizes Mertens as minus reduced Euler characteristic of squarefree integer complex; theorem3.1 identifies Betti numbers with odd squarefrees in (N/2,N], theorem3.4 total Betti count~2N/pi^2. Thus simply renaming Moebius as a SUSY/topological index leaves signed even/odd cancellation open. Literature reviewed, not formalized here.

Open high-level investigation: arithmetic concentration rigidity (classification and exclusion of normalized energy escape using literal nonlinear formation constraints). No arithmetic wave-cone theorem, compactness mechanism, or RH proof has been constructed. Standard PDE compensated-compactness theorems require constraints, mass bounds and boundary control not yet supplied here; treating a zero-free Mellin symbol as such a constraint would be circular.
