# Step 47: the unconditional floor endpoint — hline discharged [LEAN-PROVED]

Module `formal/GaloisForLFunctions/RHTower/XiResolventUnconditionalFloor.lean` (imports
XiResolventRelativeNodalCriterion), wired last in RHTower.lean. Four theorems, all
[propext, Classical.choice, Quot.sound].

## The discovery

Corpus asset `xiWard_offlinePair_height_sq_gt_sixtyfive` (XiWardCriticalBudgetProbe:738):
every off-critical ξ zero has squared ordinate > 65 ("no off-critical zero below height 8"),
UNCONDITIONAL, certified from the theta representation + the 3/50 budget — no numerical zero
location anywhere. Also there: `xi_ne_zero_of_im_sq_le` (ξ zero-free for ordinate² ≤ 32),
`riemannZeta_ne_zero_of_im_sq_le`, `card_mul_mass_le_of_height_le` (spectral counting bound),
`logDeriv_xi_one = completedRiemannZeta₀ 1`, `norm_completedRiemannZeta₀_one_le` (≤ 3/100 via
`norm_mellin_f_modif_half_le` from XiThetaExplicitBounds).

## Theorems

- `offline_height_sq_gt_sixtyfive (q) (hoff : im α ≠ 0) : 65 < (Re α)²` — chart transfer.
  Charts: XiRightZeroCopy = {q : XiZeroCopy // 0 < (I·α).re} ((I·α).re = −Im α; right ⟺
  Im α < 0); xiRightCenteredZero = I·α = ρ − 1/2, its .im = Re α = height. Left copies via
  `xiSpectralPoint_reflect` (α ↦ −α); lower Schwarz reps via `xiRightZeroCopyConjEquiv` +
  `xiRightCenteredZero_conj` (im flips), boundary excluded by
  `xiRightCenteredZero_im_ne_zero`.
- `hline_of_floor {X δ} (hX) (hδfloor : 1/(X + 259/4) ≤ δ)`: every copy with ‖u‖ ≥ δ is on
  the line. (Off-line ⟹ Re(α²+X) > 65 − 1/4 + X ⟹ ‖u‖ < 1/(X+259/4).)
- **`riemannHypothesis_iff_relative_nodal_floor {X} (hX) (P) (hPnz below floor scale)`**:
  RH ⟺ ∀ R ⊂ (0,1] finite, ∀ m, single (0,2,1) minor at X^m·(nodalPolynomial R·P) ≥ 0.
  NO line-placement hypothesis — fully unconditional scale-factored endpoint.
- `polyTuranMinor_supply_of_floor`: supply above the floor scale without hline.

## Layer 1 recipe (recorded, next campaign)

Second certified ray jet at s = 1/2 + c: (i) two-sided ‖ξ(s)‖ via even-kernel Mellin integrals
at general real s (XiThetaExplicitBounds machinery); (ii) ‖ξ'(s)‖ via log-weighted kernel
integrals (analogs of outer_mellin_piece_le/inner majorants); (iii) quotient. s = 1 was
special: logDeriv collapses to the value Λ₀(1).

## Layer 3 audit (recorded)

CM-of-Euler-ray-response mechanism is FALSE (CM ⟺ moment positivity; step-38 masking defeats
it). Meta-frame [CONJECTURE]: no finite-jet-consuming mechanism proves RH in-chart (finite
configs interpolate finite jet lists with off-line pairs). Uniform mechanism must be global —
redirect to Gauss-lane Weil-positivity/GNS square realization. The criterion lane is complete:
exact countable interface + full effectivity + unconditional floor.

Card: xic-order-one-growth-organ.md steps 44-47.
