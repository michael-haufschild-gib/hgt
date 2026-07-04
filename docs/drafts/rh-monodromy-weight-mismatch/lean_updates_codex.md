
## RHTower Lean Changes

- `CreationRate.lean`: added `pricing_close_zero`, composing `pricing_pigeonhole` with `far_kernel_lower` to produce a `c`-close contributing zero directly from the planar Poisson price.
- `MollifiedDip.lean`: added `sliverCount_le_of_average_kernel`, combining average dip input with the kernel-measure count.
- `ThickDips.lean`: added `thickSliverCount_le_of_average_floor_kernel`, combining average dips, thick-part counting, floor exclusion, and tail-kernel pricing.
- `PerturbedDip.lean`: added `exp_mul_I_ne_one_of_pos_lt_two_pi`, `polar_radius_nonneg_of_pos_lt_two_pi`, and `birthKilled_of_perturbed_rotation_explicit_polar` to feed the perturbed kill constructor from the explicit circle formula.
- `AnnealWindowRelation.lean`: added `anneal_window_parity_transport_of_domination`, transporting the window parity relation to arbitrary rung `k` from domination plus the level `2^(k+1)` seam congruence.
- Removed wrapper-only additions from `SeamSignTransport.lean`, `ZetaCarrier.lean`, and `MollifiedDip.lean`.
