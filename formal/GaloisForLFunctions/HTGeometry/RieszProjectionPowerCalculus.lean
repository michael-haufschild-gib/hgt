import GaloisForLFunctions.HTGeometry.ResolventPerturbation
import GaloisForLFunctions.HTGeometry.FiniteRankTraceDeterminant

/-!
# Powers, nested contours and the finite-rank outer part of a Riesz projection

For an element `a` of a complete normed `ℂ`-algebra and a circle `|z| = r` in the resolvent set, let
`P = (2πi)⁻¹ ∮ R(z) dz` be the Riesz projection of the enclosed spectrum and `Q = 1 − P`.

* `pow_mul_rieszProjection`: `aⁿ P = (2πi)⁻¹ ∮ zⁿ R(z) dz`, so `‖aⁿ P‖ ≤ r^{n+1} M` when
  `‖R‖ ≤ M` on the circle.  The proof writes `aⁿ R(z) = zⁿ R(z) − Σ_{j<n} z^j a^{n−1−j}`; the
  polynomial part has zero circle integral.
* `pow_mul_outerInverse`: with `G_n = −(2πi)⁻¹ ∮ z^{−n} R(z) dz` one has `aⁿ G_n = Q`
  (`n ≥ 1`), and `‖G_n‖ ≤ r M / rⁿ`.
* `rieszProjection_mul_of_lt`, `rieszProjection_mul_of_lt'`: for nested circles in the resolvent
  set, `P_r P_R = P_R P_r = P_r` — the two-contour computation needs no hypothesis on the
  annulus between them.
* `exists_closedAnnulus_subset_resolventSet`, `rieszProjection_mul_self_of_sphere`: a circle in the
  resolvent set is the inner boundary of a spectrum-free closed annulus, so `P² = P`.
* `finiteDimensional_range_one_sub_rieszProjection`: if `Tⁿ = F + S` with `F` of finite rank and
  `r M ‖S‖ < rⁿ`, the range of `Q` is finite dimensional of dimension at most the rank of `F`
  (`F` is injective on it, since there `w = G_n S w`).
* `one_sub_rieszProjection_apply_mem`: if `Tⁿ = F_n + S_n` with `F_n` mapping into a closed
  subspace `V` and `‖S_n‖/rⁿ → 0`, the range of `Q` lies in `V`.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Filter Topology

section Algebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [CompleteSpace A] in
/-- **Resolvents at two points commute.** -/
theorem commute_resolvent_resolvent {a : A} {l m : ℂ} (hl : l ∈ resolventSet ℂ a)
    (hm : m ∈ resolventSet ℂ a) :
    resolvent a l * resolvent a m = resolvent a m * resolvent a l := by
  by_cases hlm : l = m
  · rw [hlm]
  have h1 := resolvent_sub_resolvent hl hm
  have h2 := resolvent_sub_resolvent hm hl
  have hne : (m - l : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hlm)
  have h3 : (m - l) • (resolvent a l * resolvent a m) =
      (m - l) • (resolvent a m * resolvent a l) := by
    rw [← h1, show (m - l) = -(l - m) by ring, neg_smul, ← h2, neg_sub]
  exact smul_right_injective A hne h3

omit [CompleteSpace A] in
/-- `aⁿ R(z) = zⁿ R(z) − Σ_{j<n} z^j a^{n−1−j}`. -/
theorem pow_mul_resolvent_eq {a : A} {z : ℂ} (hz : z ∈ resolventSet ℂ a) (n : ℕ) :
    a ^ n * resolvent a z =
      z ^ n • resolvent a z - ∑ i ∈ Finset.range n, z ^ i • a ^ (n - 1 - i) := by
  have hc : Commute (algebraMap ℂ A z) a := Algebra.commutes z a
  have hgeom := hc.geom_sum₂_mul n
  have h1 : (algebraMap ℂ A z - a) * resolvent a z = 1 := sub_mul_resolvent hz
  have hsum : (∑ i ∈ Finset.range n, algebraMap ℂ A z ^ i * a ^ (n - 1 - i))
      = ∑ i ∈ Finset.range n, z ^ i • a ^ (n - 1 - i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_pow, ← Algebra.smul_def]
  calc a ^ n * resolvent a z
      = algebraMap ℂ A z ^ n * resolvent a z
        - (algebraMap ℂ A z ^ n - a ^ n) * resolvent a z := by noncomm_ring
    _ = algebraMap ℂ A z ^ n * resolvent a z
        - (∑ i ∈ Finset.range n, algebraMap ℂ A z ^ i * a ^ (n - 1 - i))
          * ((algebraMap ℂ A z - a) * resolvent a z) := by rw [← hgeom, mul_assoc]
    _ = z ^ n • resolvent a z - ∑ i ∈ Finset.range n, z ^ i • a ^ (n - 1 - i) := by
        rw [h1, mul_one, hsum, ← map_pow, ← Algebra.smul_def]

/-- `∮ zⁿ dz = 0` around a circle centred at `0`, for `n ≥ 0`. -/
theorem circleIntegral_pow_smul_const (b : A) (r : ℝ) (n : ℕ) :
    (∮ z in C(0, r), z ^ n • b) = 0 := by
  rw [circleIntegral.integral_smul_const]
  have h := circleIntegral.integral_sub_zpow_of_ne (n := (n : ℤ)) (by omega) 0 0 r
  simp only [sub_zero, zpow_natCast] at h
  rw [h, zero_smul]

/-- `∮ z^{j−n} dz` vanishes for `j < n − 1` and equals `2πi` for `j = n − 1`. -/
theorem circleIntegral_inv_pow_mul_pow_smul_const (b : A) {r : ℝ} (hr : 0 < r) {n j : ℕ}
    (hj : j < n) :
    (∮ z in C(0, r), (z ^ n)⁻¹ • z ^ j • b) =
      if j + 1 = n then (2 * Real.pi * Complex.I) • b else 0 := by
  have hfun : (fun z : ℂ => (z ^ n)⁻¹ • z ^ j • b) = fun z => (z - 0) ^ ((j : ℤ) - n) • b := by
    funext z
    rw [smul_smul, sub_zero]
    congr 1
    by_cases hz : z = 0
    · subst hz
      rw [zero_pow (by omega), inv_zero, zero_mul, zero_zpow _ (by omega)]
    · rw [zpow_sub₀ hz, zpow_natCast, zpow_natCast, mul_comm, div_eq_mul_inv]
  rw [hfun, circleIntegral.integral_smul_const]
  split_ifs with hjn
  · have he : (j : ℤ) - n = -1 := by omega
    rw [he, show ((fun z : ℂ => (z - 0) ^ (-1 : ℤ)) = fun z => (z - 0)⁻¹) from
      funext fun z => zpow_neg_one _, circleIntegral.integral_sub_inv_of_mem_ball
        (mem_ball_self hr)]
  · rw [circleIntegral.integral_sub_zpow_of_ne (by omega), zero_smul]

/-- **The `n`-th power times the Riesz projection is the `n`-th moment of the resolvent.** -/
theorem pow_mul_rieszProjection (a : A) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ a) (n : ℕ) :
    a ^ n * rieszProjection a 0 r =
      (2 * Real.pi * Complex.I)⁻¹ • ∮ z in C(0, r), z ^ n • resolvent a z := by
  have hci : CircleIntegrable (resolvent a) 0 r := circleIntegrable_resolvent hr h
  have hcont : ContinuousOn (resolvent a) (sphere (0 : ℂ) r) := fun z hz =>
    ((spectrum.hasDerivAt_resolvent_const_left (h z hz)).continuousAt).continuousWithinAt
  have hci1 : CircleIntegrable (fun z : ℂ => z ^ n • resolvent a z) 0 r :=
    ContinuousOn.circleIntegrable hr ((continuousOn_id.pow n).smul hcont)
  have hci2 : ∀ i ∈ Finset.range n,
      CircleIntegrable (fun z : ℂ => z ^ i • a ^ (n - 1 - i)) 0 r := fun i _ =>
    ContinuousOn.circleIntegrable hr ((continuousOn_id.pow i).smul continuousOn_const)
  have hci3 : CircleIntegrable
      (fun z : ℂ => ∑ i ∈ Finset.range n, z ^ i • a ^ (n - 1 - i)) 0 r :=
    ContinuousOn.circleIntegrable hr (continuousOn_finsetSum _ fun i _ =>
      (continuousOn_id.pow i).smul continuousOn_const)
  rw [rieszProjection, Algebra.mul_smul_comm, circleIntegral_mul_left hci]
  congr 1
  rw [circleIntegral.integral_congr hr fun z hz => pow_mul_resolvent_eq (h z hz) n,
    circleIntegral.integral_sub hci1 hci3, circleIntegral.integral_fun_sum hci2]
  simp only [circleIntegral_pow_smul_const, Finset.sum_const_zero, sub_zero]

/-- **`‖aⁿ P‖ ≤ r^{n+1} M`** when the resolvent is bounded by `M` on the circle. -/
theorem norm_pow_mul_rieszProjection_le (a : A) {r M : ℝ} (hr : 0 ≤ r)
    (h : ∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ a)
    (hM : ∀ z ∈ sphere (0 : ℂ) r, ‖resolvent a z‖ ≤ M) (n : ℕ) :
    ‖a ^ n * rieszProjection a 0 r‖ ≤ r ^ (n + 1) * M := by
  rw [pow_mul_rieszProjection a hr h n]
  have hpt : ∀ z ∈ sphere (0 : ℂ) r, ‖z ^ n • resolvent a z‖ ≤ r ^ n * M := by
    intro z hz
    rw [norm_smul, norm_pow, mem_sphere_zero_iff_norm.mp hz]
    exact mul_le_mul_of_nonneg_left (hM z hz) (pow_nonneg hr n)
  have hint := circleIntegral.norm_integral_le_of_norm_le_const hr hpt
  have hnorm : ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv]; congr 1; simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  rw [norm_smul, hnorm]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [inv_mul_eq_div, div_le_iff₀ hpi]
  calc ‖∮ z in C(0, r), z ^ n • resolvent a z‖ ≤ 2 * Real.pi * r * (r ^ n * M) := hint
    _ = r ^ (n + 1) * M * (2 * Real.pi) := by ring

/-- **The difference of two `n`-th moments**: `‖aⁿ P_a − bⁿ P_b‖ ≤ r^{n+1} · 2M²‖b − a‖`. -/
theorem norm_pow_mul_rieszProjection_sub_le (a b : A) {r M : ℝ} (hr : 0 ≤ r)
    (ha : ∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ a)
    (hM : ∀ z ∈ sphere (0 : ℂ) r, ‖resolvent a z‖ ≤ M) (hab : 2 * ‖b - a‖ * M ≤ 1) (n : ℕ) :
    ‖b ^ n * rieszProjection b 0 r - a ^ n * rieszProjection a 0 r‖ ≤
      r ^ (n + 1) * (2 * M ^ 2 * ‖b - a‖) := by
  have hb : ∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ b := fun z hz =>
    (norm_resolvent_sub_le_of_norm_sub_le (ha z hz) (hM z hz) hab).1
  have hcontb : ContinuousOn (resolvent b) (sphere (0 : ℂ) r) := fun z hz =>
    ((spectrum.hasDerivAt_resolvent_const_left (hb z hz)).continuousAt).continuousWithinAt
  have hconta : ContinuousOn (resolvent a) (sphere (0 : ℂ) r) := fun z hz =>
    ((spectrum.hasDerivAt_resolvent_const_left (ha z hz)).continuousAt).continuousWithinAt
  have hcib : CircleIntegrable (fun z : ℂ => z ^ n • resolvent b z) 0 r :=
    ContinuousOn.circleIntegrable hr ((continuousOn_id.pow n).smul hcontb)
  have hcia : CircleIntegrable (fun z : ℂ => z ^ n • resolvent a z) 0 r :=
    ContinuousOn.circleIntegrable hr ((continuousOn_id.pow n).smul hconta)
  rw [pow_mul_rieszProjection a hr ha n, pow_mul_rieszProjection b hr hb n, ← smul_sub,
    ← circleIntegral.integral_sub hcib hcia]
  have hpt : ∀ z ∈ sphere (0 : ℂ) r, ‖z ^ n • resolvent b z - z ^ n • resolvent a z‖
      ≤ r ^ n * (2 * M ^ 2 * ‖b - a‖) := by
    intro z hz
    rw [← smul_sub, norm_smul, norm_pow, mem_sphere_zero_iff_norm.mp hz]
    exact mul_le_mul_of_nonneg_left
      (norm_resolvent_sub_le_of_norm_sub_le (ha z hz) (hM z hz) hab).2 (pow_nonneg hr n)
  have hint := circleIntegral.norm_integral_le_of_norm_le_const hr hpt
  have hnorm : ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv]; congr 1; simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  rw [norm_smul, hnorm]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [inv_mul_eq_div, div_le_iff₀ hpi]
  calc _ ≤ 2 * Real.pi * r * (r ^ n * (2 * M ^ 2 * ‖b - a‖)) := hint
    _ = r ^ (n + 1) * (2 * M ^ 2 * ‖b - a‖) * (2 * Real.pi) := by ring

/-- **The perturbed resolvent bound**: a perturbation smaller than `1/(2M)` keeps the circle in the
resolvent set with resolvent bound `2M`. -/
theorem resolvent_bound_of_perturb (a b : A) {r M : ℝ}
    (ha : ∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ a)
    (hM : ∀ z ∈ sphere (0 : ℂ) r, ‖resolvent a z‖ ≤ M) (hab : 2 * ‖b - a‖ * M ≤ 1) :
    (∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ b) ∧
      ∀ z ∈ sphere (0 : ℂ) r, ‖resolvent b z‖ ≤ 2 * M := by
  refine ⟨fun z hz => (norm_resolvent_sub_le_of_norm_sub_le (ha z hz) (hM z hz) hab).1,
    fun z hz => ?_⟩
  have h := (norm_resolvent_sub_le_of_norm_sub_le (ha z hz) (hM z hz) hab).2
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM z hz)
  have h2 : 2 * M ^ 2 * ‖b - a‖ ≤ M := by nlinarith [norm_nonneg (b - a)]
  have := norm_sub_norm_le (resolvent b z) (resolvent a z)
  linarith [hM z hz]

/-! ## Nested contours -/

/-- The resolvent identity integrated over the outer circle, for two circles in the resolvent
set. -/
theorem circleIntegral_resolvent_mul_of_spheres (a : A) {r R : ℝ} (h0 : 0 < r) (hrR : r < R)
    (hR : ∀ mu ∈ sphere (0 : ℂ) R, mu ∈ resolventSet ℂ a) {lam : ℂ} (hlam : lam ∈ sphere (0 : ℂ) r)
    (hres : lam ∈ resolventSet ℂ a) :
    (∮ mu in C(0, R), resolvent a lam * resolvent a mu)
      = (2 * Real.pi * Complex.I : ℂ) • resolvent a lam - resolventCauchyTransform a 0 R lam := by
  have hRpos : 0 < R := lt_trans h0 hrR
  have hdl : dist lam 0 = r := hlam
  have hlamball : lam ∈ ball (0 : ℂ) R := by rw [mem_ball, hdl]; exact hrR
  have hne : ∀ mu ∈ sphere (0 : ℂ) R, mu - lam ≠ 0 := by
    intro mu hmu he
    have hd : dist mu 0 = R := hmu
    rw [sub_eq_zero.mp he, hdl] at hd
    linarith
  have hpt : ∀ mu ∈ sphere (0 : ℂ) R, resolvent a lam * resolvent a mu
      = (mu - lam)⁻¹ • resolvent a lam - (mu - lam)⁻¹ • resolvent a mu := by
    intro mu hmu
    rw [← smul_sub, resolvent_sub_resolvent hres (hR mu hmu), smul_smul,
      inv_mul_cancel₀ (hne mu hmu), one_smul]
  have hkern : ContinuousOn (fun mu : ℂ => (mu - lam)⁻¹) (sphere 0 R) :=
    ContinuousOn.inv₀ ((continuous_id.sub continuous_const).continuousOn) hne
  have hci1 : CircleIntegrable (fun mu => (mu - lam)⁻¹ • resolvent a lam) 0 R :=
    ContinuousOn.circleIntegrable hRpos.le (hkern.smul continuousOn_const)
  have hci2 : CircleIntegrable (fun mu => (mu - lam)⁻¹ • resolvent a mu) 0 R :=
    ContinuousOn.circleIntegrable hRpos.le (hkern.smul fun mu hmu =>
      ((spectrum.hasDerivAt_resolvent_const_left (hR mu hmu)).continuousAt).continuousWithinAt)
  rw [circleIntegral.integral_congr hRpos.le hpt, circleIntegral.integral_sub hci1 hci2,
    circleIntegral.integral_smul_const, circleIntegral.integral_sub_inv_of_mem_ball hlamball]
  rfl

/-- **Nested Riesz projections**: `P_r P_R = P_r` for `r < R`, both circles in the resolvent
set. -/
theorem rieszProjection_mul_of_lt (a : A) {r R : ℝ} (h0 : 0 < r) (hrR : r < R)
    (hr : ∀ lam ∈ sphere (0 : ℂ) r, lam ∈ resolventSet ℂ a)
    (hR : ∀ mu ∈ sphere (0 : ℂ) R, mu ∈ resolventSet ℂ a) :
    rieszProjection a 0 r * rieszProjection a 0 R = rieszProjection a 0 r := by
  have hRpos : 0 < R := lt_trans h0 hrR
  have hci_r : CircleIntegrable (resolvent a) 0 r := circleIntegrable_resolvent h0.le hr
  have hci_R : CircleIntegrable (resolvent a) 0 R := circleIntegrable_resolvent hRpos.le hR
  have hcont_r : ContinuousOn (resolvent a) (sphere (0 : ℂ) r) := fun lam hlam =>
    ((spectrum.hasDerivAt_resolvent_const_left (hr lam hlam)).continuousAt).continuousWithinAt
  have hcia : CircleIntegrable
      (fun lam => (2 * Real.pi * Complex.I : ℂ) • resolvent a lam) 0 r :=
    ContinuousOn.circleIntegrable h0.le (continuousOn_const.smul hcont_r)
  have hG : DifferentiableOn ℂ (resolventCauchyTransform a 0 R) (ball 0 R) :=
    differentiableOn_resolventCauchyTransform a hRpos hR
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 R := closedBall_subset_ball hrR
  have hciG : CircleIntegrable (resolventCauchyTransform a 0 R) 0 r :=
    ContinuousOn.circleIntegrable h0.le
      ((hG.mono hsub).continuousOn.mono sphere_subset_closedBall)
  have hG0 : (∮ lam in C(0, r), resolventCauchyTransform a 0 R lam) = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable h0.le
      Set.countable_empty ((hG.mono hsub).continuousOn) (fun z hz => ?_)
    exact hG.differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball hrR.le hz.1))
  have hcancel : ∀ Y : A,
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • ((2 * Real.pi * Complex.I : ℂ) • Y) = Y := by
    intro Y; rw [smul_smul, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_smul]
  have key : ∀ lam ∈ sphere (0 : ℂ) r, resolvent a lam * rieszProjection a 0 R
      = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ((2 * Real.pi * Complex.I : ℂ) • resolvent a lam
          - resolventCauchyTransform a 0 R lam) := by
    intro lam hlam
    rw [rieszProjection, Algebra.mul_smul_comm, circleIntegral_mul_left hci_R,
      circleIntegral_resolvent_mul_of_spheres a h0 hrR hR hlam (hr lam hlam)]
  have e1 : rieszProjection a 0 r * rieszProjection a 0 R
      = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ lam in C(0, r), resolvent a lam * rieszProjection a 0 R := by
    rw [show rieszProjection a 0 r
        = (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ lam in C(0, r), resolvent a lam from rfl,
      Algebra.smul_mul_assoc, circleIntegral_mul_right hci_r]
  have e2 : (∮ lam in C(0, r), resolvent a lam * rieszProjection a 0 R)
      = ∮ lam in C(0, r), resolvent a lam := by
    rw [circleIntegral.integral_congr h0.le key, circleIntegral.integral_smul,
      circleIntegral.integral_sub hcia hciG, circleIntegral.integral_smul, hG0, sub_zero, hcancel]
  rw [e1, e2]
  rfl

/-- Riesz projections of the same element for two circles commute. -/
theorem rieszProjection_commute_rieszProjection (a : A) {r R : ℝ} (hr0 : 0 ≤ r) (hR0 : 0 ≤ R)
    (hr : ∀ lam ∈ sphere (0 : ℂ) r, lam ∈ resolventSet ℂ a)
    (hR : ∀ mu ∈ sphere (0 : ℂ) R, mu ∈ resolventSet ℂ a) :
    rieszProjection a 0 r * rieszProjection a 0 R =
      rieszProjection a 0 R * rieszProjection a 0 r := by
  have hci_r : CircleIntegrable (resolvent a) 0 r := circleIntegrable_resolvent hr0 hr
  have hci_R : CircleIntegrable (resolvent a) 0 R := circleIntegrable_resolvent hR0 hR
  have hcomm : ∀ lam ∈ sphere (0 : ℂ) r,
      resolvent a lam * rieszProjection a 0 R = rieszProjection a 0 R * resolvent a lam := by
    intro lam hlam
    rw [rieszProjection, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      circleIntegral_mul_left hci_R, circleIntegral_mul_right hci_R]
    congr 1
    exact circleIntegral.integral_congr hR0 fun mu hmu =>
      commute_resolvent_resolvent (hr lam hlam) (hR mu hmu)
  rw [show rieszProjection a 0 r
      = (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ lam in C(0, r), resolvent a lam from rfl,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, circleIntegral_mul_right hci_r,
    circleIntegral_mul_left hci_r]
  congr 1
  exact circleIntegral.integral_congr hr0 hcomm

/-- **Nested Riesz projections**, the other order: `P_R P_r = P_r`. -/
theorem rieszProjection_mul_of_lt' (a : A) {r R : ℝ} (h0 : 0 < r) (hrR : r < R)
    (hr : ∀ lam ∈ sphere (0 : ℂ) r, lam ∈ resolventSet ℂ a)
    (hR : ∀ mu ∈ sphere (0 : ℂ) R, mu ∈ resolventSet ℂ a) :
    rieszProjection a 0 R * rieszProjection a 0 r = rieszProjection a 0 r := by
  rw [← rieszProjection_commute_rieszProjection a h0.le (h0.le.trans hrR.le) hr hR,
    rieszProjection_mul_of_lt a h0 hrR hr hR]

/-- **A circle in the resolvent set bounds a spectrum-free closed annulus.** -/
theorem exists_closedAnnulus_subset_resolventSet (a : A) {r : ℝ} (hr : 0 < r)
    (h : ∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ a) :
    ∃ R, r < R ∧ ∀ z ∈ closedBall (0 : ℂ) R \ ball 0 r, z ∈ resolventSet ℂ a := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_sphere (0 : ℂ) r).exists_thickening_subset_open
    (spectrum.isOpen_resolventSet a) h
  refine ⟨r + δ / 2, by linarith, fun z hz => hsub ?_⟩
  have hz1 : ‖z‖ ≤ r + δ / 2 := mem_closedBall_zero_iff.mp hz.1
  have hz2 : r ≤ ‖z‖ := not_lt.mp fun hlt => hz.2 (mem_ball_zero_iff.mpr hlt)
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hz2; linarith
  have hnz : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  rw [Metric.mem_thickening_iff]
  refine ⟨((r / ‖z‖ : ℝ) : ℂ) * z, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hr.le hnz.le), div_mul_cancel₀ _ hnz.ne']
  · rw [dist_eq_norm]
    have he : z - ((r / ‖z‖ : ℝ) : ℂ) * z = ((1 - r / ‖z‖ : ℝ) : ℂ) * z := by
      push_cast; ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h01 : 0 ≤ 1 - r / ‖z‖ := by
      rw [sub_nonneg, div_le_one hnz]; exact hz2
    rw [abs_of_nonneg h01, sub_mul, one_mul, div_mul_cancel₀ _ hnz.ne']
    linarith

/-- **The Riesz projection of a circle in the resolvent set is idempotent.** -/
theorem rieszProjection_mul_self_of_sphere (a : A) {r : ℝ} (hr : 0 < r)
    (h : ∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ a) :
    rieszProjection a 0 r * rieszProjection a 0 r = rieszProjection a 0 r := by
  obtain ⟨R, hrR, hann⟩ := exists_closedAnnulus_subset_resolventSet a hr h
  exact rieszProjection_mul_self a hr hrR hann

/-! ## The outer inverse -/

/-- The **outer inverse** `G_n = −(2πi)⁻¹ ∮ z^{−n} R(z) dz`, the inverse of `aⁿ` on the range of
`1 − P`. -/
noncomputable def outerInverse (a : A) (r : ℝ) (n : ℕ) : A :=
  -((2 * Real.pi * Complex.I)⁻¹ • ∮ z in C(0, r), (z ^ n)⁻¹ • resolvent a z)

/-- **`aⁿ G_n = 1 − P`** for `n ≥ 1`. -/
theorem pow_mul_outerInverse (a : A) {r : ℝ} (hr : 0 < r)
    (h : ∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ a) {n : ℕ} (hn : 1 ≤ n) :
    a ^ n * outerInverse a r n = 1 - rieszProjection a 0 r := by
  have hcont : ContinuousOn (resolvent a) (sphere (0 : ℂ) r) := fun z hz =>
    ((spectrum.hasDerivAt_resolvent_const_left (h z hz)).continuousAt).continuousWithinAt
  have hz0 : ∀ z ∈ sphere (0 : ℂ) r, z ^ n ≠ 0 := fun z hz =>
    pow_ne_zero _ (ne_zero_of_mem_sphere hr.ne' ⟨z, hz⟩)
  have hinvc : ContinuousOn (fun z : ℂ => (z ^ n)⁻¹) (sphere 0 r) :=
    (continuousOn_id.pow n).inv₀ hz0
  have hciG : CircleIntegrable (fun z : ℂ => (z ^ n)⁻¹ • resolvent a z) 0 r :=
    ContinuousOn.circleIntegrable hr.le (hinvc.smul hcont)
  have hci_res : CircleIntegrable (resolvent a) 0 r := circleIntegrable_resolvent hr.le h
  have hci2 : ∀ i ∈ Finset.range n,
      CircleIntegrable (fun z : ℂ => (z ^ n)⁻¹ • z ^ i • a ^ (n - 1 - i)) 0 r := fun i _ =>
    ContinuousOn.circleIntegrable hr.le
      (hinvc.smul ((continuousOn_id.pow i).smul continuousOn_const))
  have hpt : ∀ z ∈ sphere (0 : ℂ) r, a ^ n * ((z ^ n)⁻¹ • resolvent a z)
      = resolvent a z - ∑ i ∈ Finset.range n, (z ^ n)⁻¹ • z ^ i • a ^ (n - 1 - i) := by
    intro z hz
    rw [Algebra.mul_smul_comm, pow_mul_resolvent_eq (h z hz) n, smul_sub, smul_smul,
      inv_mul_cancel₀ (hz0 z hz), one_smul, Finset.smul_sum]
  have hsum : (∑ i ∈ Finset.range n, ∮ z in C(0, r), (z ^ n)⁻¹ • z ^ i • a ^ (n - 1 - i))
      = (2 * Real.pi * Complex.I) • (1 : A) := by
    rw [Finset.sum_congr rfl fun i hi =>
      circleIntegral_inv_pow_mul_pow_smul_const (a ^ (n - 1 - i)) hr (Finset.mem_range.mp hi)]
    simp only [show ∀ i, (i + 1 = n ↔ n - 1 = i) from fun i => by omega]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (by omega)), Nat.sub_self, pow_zero]
  have hci3 : CircleIntegrable
      (fun z : ℂ => ∑ i ∈ Finset.range n, (z ^ n)⁻¹ • z ^ i • a ^ (n - 1 - i)) 0 r :=
    ContinuousOn.circleIntegrable hr.le (continuousOn_finsetSum _ fun i _ =>
      hinvc.smul ((continuousOn_id.pow i).smul continuousOn_const))
  rw [outerInverse, mul_neg, Algebra.mul_smul_comm, circleIntegral_mul_left hciG,
    circleIntegral.integral_congr hr.le hpt,
    circleIntegral.integral_sub hci_res hci3,
    circleIntegral.integral_fun_sum hci2, hsum, smul_sub, smul_smul,
    inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_smul, rieszProjection, neg_sub]

/-- **The outer inverse commutes with the element.** -/
theorem commute_outerInverse (a : A) {r : ℝ} (hr : 0 < r)
    (h : ∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ a) (n : ℕ) :
    a * outerInverse a r n = outerInverse a r n * a := by
  have hcont : ContinuousOn (resolvent a) (sphere (0 : ℂ) r) := fun z hz =>
    ((spectrum.hasDerivAt_resolvent_const_left (h z hz)).continuousAt).continuousWithinAt
  have hz0 : ∀ z ∈ sphere (0 : ℂ) r, z ^ n ≠ 0 := fun z hz =>
    pow_ne_zero _ (ne_zero_of_mem_sphere hr.ne' ⟨z, hz⟩)
  have hciG : CircleIntegrable (fun z : ℂ => (z ^ n)⁻¹ • resolvent a z) 0 r :=
    ContinuousOn.circleIntegrable hr.le (((continuousOn_id.pow n).inv₀ hz0).smul hcont)
  rw [outerInverse, mul_neg, neg_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    circleIntegral_mul_left hciG, circleIntegral_mul_right hciG]
  congr 2
  refine circleIntegral.integral_congr hr.le fun z hz => ?_
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, commute_resolvent a (h z hz)]

omit [CompleteSpace A] in
/-- **`‖G_n‖ ≤ r M / rⁿ`.** -/
theorem norm_outerInverse_le (a : A) {r M : ℝ} (hr : 0 < r)
    (hM : ∀ z ∈ sphere (0 : ℂ) r, ‖resolvent a z‖ ≤ M) (n : ℕ) :
    ‖outerInverse a r n‖ ≤ r * M / r ^ n := by
  have hpt : ∀ z ∈ sphere (0 : ℂ) r, ‖(z ^ n)⁻¹ • resolvent a z‖ ≤ M / r ^ n := by
    intro z hz
    rw [norm_smul, norm_inv, norm_pow, mem_sphere_zero_iff_norm.mp hz, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (hM z hz) (pow_nonneg hr.le n)
  have hint := circleIntegral.norm_integral_le_of_norm_le_const hr.le hpt
  have hnorm : ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv]; congr 1; simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  rw [outerInverse, norm_neg, norm_smul, hnorm]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [inv_mul_eq_div, div_le_iff₀ hpi]
  calc _ ≤ 2 * Real.pi * r * (M / r ^ n) := hint
    _ = r * M / r ^ n * (2 * Real.pi) := by ring

end Algebra

/-! ## Finite rank of the outer part of an operator -/

section Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

open FiniteRank

/-- **The outer spectral part has finite rank.**  If `Tⁿ = F + S` with `F` of finite rank and
`r M ‖S‖ < rⁿ`, then `F` is injective on the range of `Q = 1 − P`: there `w = G_n Tⁿ w = G_n S w`
for `w ∈ ker F`, and `‖G_n S‖ < 1`. -/
theorem finiteDimensional_range_one_sub_rieszProjection (T : E →L[ℂ] E) {r M : ℝ} (hr : 0 < r)
    (h : ∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ T)
    (hM : ∀ z ∈ sphere (0 : ℂ) r, ‖resolvent T z‖ ≤ M) {n : ℕ} (hn : 1 ≤ n)
    (F S : E →L[ℂ] E) (hTFS : T ^ n = F + S) [FiniteDimensional ℂ (opRange F)]
    (hsmall : r * M * ‖S‖ < r ^ n) :
    FiniteDimensional ℂ (opRange (1 - rieszProjection T 0 r)) ∧
      Module.finrank ℂ (opRange (1 - rieszProjection T 0 r)) ≤ Module.finrank ℂ (opRange F) := by
  set P := rieszProjection T 0 r
  set Q : E →L[ℂ] E := 1 - P
  set G := outerInverse T r n
  have hPP : P * P = P := rieszProjection_mul_self_of_sphere T hr h
  have hQQ : Q * Q = Q := by
    simp only [Q, sub_mul, mul_sub, one_mul, mul_one, hPP, sub_self, sub_zero]
  have hTG : T ^ n * G = Q := pow_mul_outerInverse T hr h hn
  have hGT : G * T ^ n = Q := by
    have hc : Commute T G := commute_outerInverse T hr h n
    rw [← (hc.pow_left n).eq, hTG]
  have hGn : ‖G‖ ≤ r * M / r ^ n := norm_outerInverse_le T hr hM n
  have hrn : 0 < r ^ n := pow_pos hr n
  have hGS : ‖G‖ * ‖S‖ < 1 := by
    calc ‖G‖ * ‖S‖ ≤ r * M / r ^ n * ‖S‖ := mul_le_mul_of_nonneg_right hGn (norm_nonneg _)
      _ = r * M * ‖S‖ / r ^ n := by ring
      _ < 1 := by rw [div_lt_one hrn]; exact hsmall
  have hfix : ∀ w ∈ opRange Q, Q w = w := by
    rintro _ ⟨v, rfl⟩
    show (Q * Q) v = Q v
    rw [hQQ]
  let Φ : opRange Q →ₗ[ℂ] opRange F :=
    { toFun := fun w => ⟨F w, mem_opRange F w⟩
      map_add' := fun w₁ w₂ => by ext; simp
      map_smul' := fun c w => by ext; simp }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hFw : F w = 0 := congrArg Subtype.val hw
    have hw' : (w : E) = G (S w) := by
      calc (w : E) = Q w := (hfix w w.2).symm
        _ = (G * T ^ n) w := by rw [hGT]
        _ = G (F w + S w) := by
            show G ((T ^ n) w) = _
            rw [hTFS]; rfl
        _ = G (S w) := by rw [hFw, zero_add]
    have hle : ‖(w : E)‖ ≤ ‖G‖ * ‖S‖ * ‖(w : E)‖ := by
      calc ‖(w : E)‖ = ‖G (S w)‖ := by rw [← hw']
        _ ≤ ‖G‖ * ‖S w‖ := G.le_opNorm _
        _ ≤ ‖G‖ * (‖S‖ * ‖(w : E)‖) :=
            mul_le_mul_of_nonneg_left (S.le_opNorm _) (norm_nonneg _)
        _ = ‖G‖ * ‖S‖ * ‖(w : E)‖ := by ring
    have h0 : ‖(w : E)‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖(w : E)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      have := lt_of_le_of_lt hle (by nlinarith)
      exact lt_irrefl _ this
    exact Subtype.ext (norm_eq_zero.mp h0)
  exact ⟨Module.Finite.of_injective Φ hinj, LinearMap.finrank_le_finrank_of_injective hinj⟩

/-- **The outer spectral part lies in every closed subspace that absorbs the finite-rank parts of
the powers.** -/
theorem one_sub_rieszProjection_apply_mem (T : E →L[ℂ] E) {r M : ℝ} (hr : 0 < r)
    (h : ∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ T)
    (hM : ∀ z ∈ sphere (0 : ℂ) r, ‖resolvent T z‖ ≤ M) (V : Submodule ℂ E)
    (hV : IsClosed (V : Set E)) (F S : ℕ → E →L[ℂ] E)
    (hTFS : ∀ n, 1 ≤ n → T ^ n = F n + S n) (hF : ∀ n v, 1 ≤ n → F n v ∈ V)
    (hS : Tendsto (fun n => ‖S n‖ / r ^ n) atTop (𝓝 0)) (w : E) :
    (1 - rieszProjection T 0 r) w ∈ V := by
  set Q : E →L[ℂ] E := 1 - rieszProjection T 0 r
  have hseq : ∀ n, 1 ≤ n → Q w - F n (outerInverse T r n w) = S n (outerInverse T r n w) := by
    intro n hn
    have : Q w = (T ^ n) (outerInverse T r n w) := by
      show (1 - rieszProjection T 0 r) w = _
      rw [← pow_mul_outerInverse T hr h hn]; rfl
    rw [this, hTFS n hn]
    simp
  have hbound : ∀ n, 1 ≤ n →
      ‖Q w - F n (outerInverse T r n w)‖ ≤ ‖S n‖ / r ^ n * (r * M * ‖w‖) := by
    intro n hn
    rw [hseq n hn]
    have hrn : 0 < r ^ n := pow_pos hr n
    calc ‖S n (outerInverse T r n w)‖ ≤ ‖S n‖ * ‖outerInverse T r n w‖ := (S n).le_opNorm _
      _ ≤ ‖S n‖ * (r * M / r ^ n * ‖w‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact ((outerInverse T r n).le_opNorm w).trans
            (mul_le_mul_of_nonneg_right (norm_outerInverse_le T hr hM n) (norm_nonneg _))
      _ = ‖S n‖ / r ^ n * (r * M * ‖w‖) := by field_simp
  have hlim : Tendsto (fun n => F n (outerInverse T r n w)) atTop (𝓝 (Q w)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun n => ‖S n‖ / r ^ n * (r * M * ‖w‖)) atTop (𝓝 0) := by
      simpa using hS.mul_const (r * M * ‖w‖)
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ h0
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [norm_sub_rev]
    exact hbound n hn
  exact hV.mem_of_tendsto hlim (eventually_ge_atTop 1 |>.mono fun n hn => hF n _ hn)

end Operator

end GaloisForLFunctions.HTGeometry
