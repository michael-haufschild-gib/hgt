# Step 48: the unconditional Weil-positivity cone [LEAN-PROVED]

Module `formal/GaloisForLFunctions/RHTower/GaussHodgeWeilPositivityCone.lean` (imports
GaussHodgeWeilDeviationMoment + XiResolventUnconditionalFloor), wired last in RHTower.lean.
Four theorems, all [propext, Classical.choice, Quot.sound]. FIRST module fusing the criterion
lane (steps 36-47) into the Gauss/Weil lane (steps 1-13).

## Theorems

- `deviation_support_subset_tail`: Function.support of the deviation summand
  (Im α)²·‖dslope F (conj α) α‖² ⊆ {65 ≤ (Re α)²} — via `offline_height_sq_gt_sixtyfive`.
- `deviation_moment_le_of_tail_dominated {X}(hX){F}(hF : XiWeilSquareSummable F){C c}(hC)(hc :
  1/2 ≤ c)(hΔ : tail domination by C·‖xiResolventPoint X q‖)`: deviation moment ≤
  C·((65+(c+1/2)²)/(2c(65−1/4))·2Re(logDeriv ξ(1/2+c))). Proof: support-subtype rewrite
  (`tsum_subtype_eq_of_support_subset`), subtype tsum_le_tsum, `tsum_mul_left`, then
  `tsum_norm_xiResolventPoint_tail_le_logDeriv` at T = 65.
- `xiWeilPolarization_re_nonneg_of_tail_dominated`: the cone — 0 ≤ Re W(F,F) whenever even
  energy ≥ the ray-jet bound (via `xiWeilPolarization_re_eq_deviation_moment`).
- `xiWeilPolarization_re_nonneg_of_tail_dominated_numeric`: c = 1/2 instance — C·396/6475 ≤
  Σ‖xiWeilEvenPart F (α_q)‖² suffices (via logDeriv_xi_one + norm_completedRiemannZeta₀_one_le;
  prefactor (65+1)/64.75 = 264/259; 264/259·3/50 = 396/6475).

## Significance

First unconditional Weil-positivity theorem in the corpus beyond interface algebra. The
producer's burden inside the cone is paid by certified spectral geometry (Ward floor + 3/50
budget + surrogate); outside the cone positivity IS RH (step-13 verdict). Distinct mechanism
from the classical narrow-support unconditional positivity genre (support width kills prime
terms; ours constrains the divisor side). [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] provisional.

## The new Layer-3 handle: floor-height → cone-width law

Higher certified floors widen the cone: if the Ward machinery certifies off-line height² > H
(currently 65) then the cone constant scales like ~(prefactor(H,c)·jet) → 0 as H → ∞ with
c ≍ √H. RH = the cone exhausting test space = H → ∞. The Ward budget program (larger probes,
sharper budgets) is now DIRECTLY a Weil-positivity program. Next: populate the cone with
concrete tests (resolvent kernels F_w(z) = (z²+w)⁻¹, dslope decays like ‖u‖), certified jets
for larger probes, quantify cone-width(H).

Card: xic-order-one-growth-organ.md step 48; Gauss hub step 14.
