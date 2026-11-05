# The local Weil kernel and its contact singularity

- **ID:** R0411-WEIL-KERNEL
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0411/obstacles-summary.md` §2.5.1
- **Statement:** Before contact, the literal completed Weil form has an entire Fourier realization, unitary zero-moving, antiunitary conjugation, and an explicit Hermite–Biehler kernel. At finite contact some diagonal kernel diverges monotonically, while window positivity persists.

## Exact construction

For `0<a<a*(ζ)`, let `H_a` be the completed unshifted Weil space. Its norm is
equivalent to the original closed-form norm. Physical compact-L² Fourier evaluation
therefore extends continuously to `H_a`; its transform is entire of exponential
type at most `a`. Fourier uniqueness makes this realization injective. Smooth
normalized test functions make evaluation surjective at every complex point.
The existing isometric aperture inclusions preserve these entire transforms.

Let `D=i∂` on the smooth core. Integration by parts makes `D` symmetric for the
literal Weil form. Compact division solves `(D−κ)u=f` whenever the transform of
`f` vanishes at `κ`. Subtracting a normalized smooth evaluation vector makes this
core dense in the completed evaluation kernel. The shifts `D−κ` and `D−conj κ`
have equal Gram forms, so completion gives a unitary `U_κ` with

`(z−κ)F(U_κf)(z)=(z−conj κ)F(f)(z)`.

Conjugate reflection `f♯(x)=conj(f(−x))` preserves every diagonal Weil summand.
Its dense-core extension is an antiunitary involution with
`F(f♯)(z)=conj(F(f)(conj z))`.

Write `v_z` for the Riesz vector of evaluation, `K(w,z)=F(v_w)(z)`, and
`k=‖v_i‖²>0`. Define `E(z)=(z+i)K(i,z)`. Zero-moving intertwines the
orthogonal projections of evaluation vectors onto the two kernels at `±i`.
Their inner products give

`E(z)conj(E(w))−E♯(z)conj(E♯(w))=2ik(conj(w)−z)K(w,z)`.

On the diagonal this is
`|E(z)|²−|E♯(z)|²=4 Im(z) k ‖v_z‖²`.
Surjective evaluation proves strict Hermite–Biehler inequality in the upper
half-plane. A real zero of `E` would force `K(x,z)=0` for `z≠x`; continuity,
Fourier uniqueness, and `v_x≠0` exclude it.

## Contact

Isometric aperture inclusion and Cauchy–Schwarz make `‖v_z‖²` monotone in `a`.
If contact is finite, the actual ground vector `q` has `Q(q)=0` and nonzero
physical source. Choose `z` with `F(q)(z)≠0`. A common bound `C` for earlier
diagonal kernels would give `|F(f)(z)|²≤C Q(f)` on every strictly interior
smooth source: each belongs to a smaller aperture. Both sides are continuous
in the contact closed-form norm, so density extends this inequality to `q`,
a contradiction. Monotonicity strengthens unboundedness to divergence along
all sufficiently large pre-contact apertures.

The unconditional alternative is therefore: RH holds, or there is a finite
contact aperture, positive as a window, with a fixed Fourier evaluation whose
diagonal kernels tend to infinity below contact.

## Lean

Files lie in `formal/GaloisForLFunctions/CanonicalSystemOfTheWindowTower/`.
The first four rows use namespace
`GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact`;
the last uses its parent namespace.

| Module | Main declarations |
|---|---|
| `ThePrecontactWeilSpacesHaveEntireFourierCoordinates` | `differentiable_fourier`, `fourier_exponentialType`, `eval_surjective`, `fourier_injective`, `fourier_inclusion` |
| `ZeroMovingIsUnitaryBeforeContact` | `zeroMove`, `zeroMove_fourier`, `exists_zero_move` |
| `ConjugationPreservesThePrecontactWeilSpace` | `sharp`, `fourier_sharp`, `sharp_involutive` |
| `TheLocalWeilKernelIsHermiteBiehler` | `kernel_christoffelDarboux`, `hermiteBiehler_norm_difference`, `hermiteBiehler_strict`, `hermiteBiehler_ne_zero_ofReal` |
| `TheWeilKernelDivergesAtContact` | `riemannHypothesis_or_kernel_tends_to_top_at_contact`, `riemannHypothesis_or_positive_contact_with_unbounded_kernel` |

Transitive axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.
All modules are imported by the programme umbrella.

## Remaining target

This constructs the exact local kernel chain and identifies its finite contact
singularity. It does not yet construct reflection evolution in the literal
length coordinate or its prime-power entry law. The local normalization of `E`
alone supplies neither aperture differentiation nor a compatible Hamiltonian.
