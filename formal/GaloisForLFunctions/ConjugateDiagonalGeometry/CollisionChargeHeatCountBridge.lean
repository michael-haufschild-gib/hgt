import GaloisForLFunctions.ConjugateDiagonalGeometry.CollisionChargeIncrements
import GaloisForLFunctions.RHTower.KiKimLeeEffectiveReality
import GaloisForLFunctions.RHTower.DeBruijnCollisionMassAndCriticalHeat
import GaloisForLFunctions.RHTower.Heat.HeatUniformDepthZeroDensity
import GaloisForLFunctions.RHTower.RiemannXiRealAxisNonvanishing
import GaloisForLFunctions.HTGeometry.HeatFlowDepthCountFails

/-!
# Quantitative bridges and obstructions between collision charge `O(T)` and heat count `N(t)`

We test the conjecture `N(t) ≤ O(2π e^{40/t} + C)` linking the de Bruijn–Newman nonreal zero count
`N(t) = nonrealZeroCount t` (`H_t(z) = 0`, `Im z ≠ 0`) to the cumulative horizontal collision
charge `O(T) = xiHorizontalCollisionCharge T` (`0 < Re ρ < 1`, `0 ≤ Im ρ < T`), isolate the two
exact mathematical obstructions to the literal unnormalized/unbuffered inequality, and prove the
unconditional normalized moving-barrier, global, and reverse dyadic bridges:

1. **Four-quadrant parity accounting and minimal-fibre falsification**
   (`nonrealZeroCount_eq_two_mul_upperHalfNonrealZeroCount`,
   `xiWindowNonrealZeroCount_eq_two_mul_offLineOrder`,
   `xiWindowNonrealZeroCount_le_two_mul_collisionCharge`,
   `eventually_nonrealZeroCount_le_collisionCharge_iff_rh_of_minimal_fibres`):
   Conjugation splits `N(t) = 2 N_↑(t)` (`upperHalfNonrealZeroCount t`, `Im z > 0`). At `t = 0`,
   `ξ(σ) ≠ 0` on `ℝ` (`xi_ne_zero_of_ofReal`) and `H_0(-z) = H_0(z)` yield
   `xiWindowNonrealZeroCount T = 2 * xiStripWindowOffLineOrder T ≤ 2 * O(T)`. Under finite
   off-line count and minimal horizontal off-line fibres (`m_ρ = 1`, `H(Im ρ) = 2`), `O(U)` equals
   `xiStripWindowOffLineOrder U`, so `∀ᶠ t in 𝓝[>] 0, N(t) ≤ O(f(t))` is equivalent to
   `RiemannHypothesis` for *every* height function `f : ℝ → ℝ` (violated as `4k ≤ 2k` when `k ≥ 1`
   minimal quartets exist).

2. **Cubic Calogero–Moser inward-drift obstruction to `C = 0` window monotonicity**
   (`exists_polyHeat_nonreal_root_inward_drift`):
   For every height `A > 1/4`, the real polynomial `P_A(z) = ((z − A)² + 4)(z − (A + 1/2))` has
   all nonreal roots on the boundary `|Re z| = A` (`0` nonreal roots in `|Re z| < A`), yet at
   `t = 1/4` the outward repulsion of the nearby real zero `A + 1/2` pushes the conjugate pair
   strictly inward into `|Re z| < A` (`2` nonreal roots in `|Re z| < A`).

3. **Forward real-zero stability at `t = 0` and moving-barrier windowed descent**
   (`exists_ball_real_zeros_forward_nonneg`,
   `nonrealZeroCount_le_two_mul_collisionCharge_of_barrier`,
   `upperHalfNonrealZeroCount_le_collisionCharge_of_barrier`):
   Extending `exists_ball_real_zeros_forward` to `t ≥ 0` via clamped locally uniform convergence on
   `𝓝[>] s₀`, any continuous barrier `R` on `[0, t]` (`0 < t ≤ 1/8`) with `2π e^{40/t} ≤ R(t)` and
   no nonreal zeros of `H_s` on `|Re z| = R(s)` yields `N(t) ≤ 2 O(R(0))` and `N_↑(t) ≤ O(R(0))`.

4. **Unconditional global heat-by-charge bound and finiteness equivalence**
   (`nonrealZeroCount_le_two_mul_of_collisionCharge_bdd`,
   `upperHalfNonrealZeroCount_le_of_collisionCharge_bdd`,
   `exists_nonrealZeroCount_le_iff_exists_collisionCharge_le`):
   If `O(T) ≤ M` for all `T ≥ 0`, then `N(t) ≤ 2M` and `N_↑(t) ≤ M` for all `t > 0`, closing
   `(∃ B, ∀ t > 0, N(t) ≤ B) ↔ (∃ M, ∀ T ≥ 0, O(T) ≤ M)`.

5. **Reverse dyadic finite-height heat-to-charge bound**
   (`exists_dyadicCollisionCharge_le_log_sq_mul_nonrealZeroCount_add_shallow`):
   Combining general interval collision-charge bounds with uniform-depth heat persistence yields
   `O(2X) − O(X) ≤ C₁ (log X)² N(t) + C₂ (log X) n_{off, < d}([X, 2X))` for `X ≥ X₀`,
   `0 < d ≤ 1/2`, and `0 < t ≤ c d² / log X`.
-/

set_option autoImplicit false

open Complex Filter Topology Set Metric Polynomial
open scoped BigOperators
open _root_.RHTower _root_.RHTower.DeBruijn GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

/-! ## §1. Quadrant accounting, unheated window count, and minimal-fibre parity obstruction -/

/-- Upper-half-plane nonreal zero count `N_↑(t)` of `H_t` (`Im z > 0`, counted with multiplicity;
`0` for `t ≤ 0`). -/
def upperHalfNonrealZeroCount (t : ℝ) : ℕ :=
  if ht : 0 < t then
    ∑ z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset.filter (fun z => 0 < z.im),
      zeroMult (riemannHeat t) z
  else 0

theorem upperHalfNonrealZeroCount_eq {t : ℝ} (ht : 0 < t) :
    upperHalfNonrealZeroCount t =
      ∑ z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset.filter (fun z => 0 < z.im),
        zeroMult (riemannHeat t) z :=
  dif_pos ht

/-- **Conjugate half-plane halving.** `N(t) = 2 N_↑(t)` for every `t ∈ ℝ`. -/
theorem nonrealZeroCount_eq_two_mul_upperHalfNonrealZeroCount (t : ℝ) :
    nonrealZeroCount t = 2 * upperHalfNonrealZeroCount t := by
  classical
  by_cases ht : 0 < t
  · rw [nonrealZeroCount_eq ht, upperHalfNonrealZeroCount_eq ht]
    set F := (riemannHeat_nonreal_zeros_finite ht).toFinset
    have hsplit := (Finset.sum_filter_add_sum_filter_not F (fun z => 0 < z.im)
      (fun z => zeroMult (riemannHeat t) z)).symm
    have hbij : ∑ z ∈ F.filter (fun z => ¬ 0 < z.im), zeroMult (riemannHeat t) z =
        ∑ z ∈ F.filter (fun z => 0 < z.im), zeroMult (riemannHeat t) z := by
      refine Finset.sum_bij (fun z _ => (starRingEnd ℂ) z) (fun z hz => ?_) (fun a _ b _ h => ?_)
        (fun w hw => ?_) (fun z _ => (zeroMult_riemannHeat_conj ht.le z).symm)
      · obtain ⟨hzF, hle⟩ := Finset.mem_filter.mp hz
        obtain ⟨hz0, hzim⟩ := (Set.Finite.mem_toFinset _).mp hzF
        have hlt : z.im < 0 := lt_of_le_of_ne (not_lt.mp hle) hzim
        refine Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr ⟨?_, ?_⟩, ?_⟩
        · rw [riemannHeat_conj ht.le, hz0, map_zero]
        · simp [hzim]
        · simp; linarith
      · exact (starRingEnd ℂ).injective h
      · obtain ⟨hwF, hwpos⟩ := Finset.mem_filter.mp hw
        obtain ⟨hw0, hwim⟩ := (Set.Finite.mem_toFinset _).mp hwF
        refine ⟨(starRingEnd ℂ) w, Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr ⟨?_, ?_⟩, ?_⟩,
          Complex.conj_conj w⟩
        · rw [riemannHeat_conj ht.le, hw0, map_zero]
        · simp [hwim]
        · simp; linarith
    rw [hsplit, hbij, two_mul]
  · simp [nonrealZeroCount, upperHalfNonrealZeroCount, ht]

/-- `riemannHeat 0 z = 0` forces `|z.im| < 1/2` (open critical strip `0 < Re ρ < 1`). -/
theorem abs_im_lt_half_of_riemannHeat_zero {z : ℂ} (hz : riemannHeat 0 z = 0) :
    |z.im| < 1 / 2 := by
  rw [riemannHeat_zero] at hz
  have hstrip := (CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp
    (CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_of_xi_eq_zero hz)).2
  have hre : ((1 / 2 : ℂ) + I * z).re = 1 / 2 - z.im := by simp; ring
  rw [hre] at hstrip
  rw [abs_lt]
  exact ⟨by linarith [hstrip.2], by linarith [hstrip.1]⟩

/-- `riemannHeat 0` has no zeros on the imaginary axis `Re z = 0` (`ξ` has no real zeros). -/
theorem re_ne_zero_of_riemannHeat_zero {z : ℂ} (hz : riemannHeat 0 z = 0) :
    z.re ≠ 0 := by
  intro hre
  rw [riemannHeat_zero] at hz
  have heq : (1 / 2 : ℂ) + I * z = ((1 / 2 - z.im : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hre]; ring
    · simp [hre]
  rw [heq] at hz
  exact xi_ne_zero_of_ofReal (1 / 2 - z.im) hz

/-- Every zero in `stripZeros T` has strictly positive imaginary part (`ξ` vanishes nowhere on `ℝ`). -/
theorem im_pos_of_mem_stripZeros {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ (stripZeros_finite T).toFinset) :
    0 < ρ.im := by
  obtain ⟨⟨_, _, him0, _⟩, hxi⟩ := (Set.Finite.mem_toFinset _).mp hρ
  refine lt_of_le_of_ne him0 fun h0 => ?_
  have heq : ρ = (ρ.re : ℂ) := Complex.ext rfl h0.symm
  rw [heq] at hxi
  exact xi_ne_zero_of_ofReal ρ.re hxi

/-- Finiteness of the nonreal zeros of `H_0 = Ξ` in any horizontal window `|Re z| < T`. -/
theorem riemannHeat_zero_window_zeros_finite (T : ℝ) :
    {z : ℂ | riemannHeat 0 z = 0 ∧ z.im ≠ 0 ∧ |z.re| < T}.Finite := by
  set R : ℝ := max T 0 + 1
  have han : AnalyticOnNhd ℂ (riemannHeat 0) (closedBall 0 R) := fun z _ =>
    (differentiable_riemannHeat le_rfl).analyticAt z
  have hfin := finite_zeros_closedBall han (fun z _ h =>
    analyticOrderAt_riemannHeat_ne_top le_rfl z (analyticOrderAt_eq_top.mpr h))
  refine hfin.subset fun z ⟨hz0, _, hzre⟩ => ⟨?_, hz0⟩
  rw [mem_closedBall, dist_zero_right]
  have him := (abs_im_lt_half_of_riemannHeat_zero hz0).le
  have hnorm := Complex.norm_le_abs_re_add_abs_im z
  have hT : T ≤ max T 0 := le_max_left _ _
  linarith

/-- Unheated nonreal zero count of `H_0 = Ξ` in the symmetric window `|Re z| < T`. -/
def xiWindowNonrealZeroCount (T : ℝ) : ℕ :=
  ∑ z ∈ (riemannHeat_zero_window_zeros_finite T).toFinset, zeroMult (riemannHeat 0) z

/-- Multiplicity of `H_s` (`s ≥ 0`) is invariant under `z ↦ −z`. -/
theorem zeroMult_riemannHeat_neg {s : ℝ} (hs : 0 ≤ s) (z : ℂ) :
    zeroMult (riemannHeat s) (-z) = zeroMult (riemannHeat s) z := by
  have hH := differentiable_riemannHeat hs
  suffices analyticOrderAt (riemannHeat s) (-z) = analyticOrderAt (riemannHeat s) z by
    rw [zeroMult, zeroMult, this]
  refine ENat.eq_of_forall_natCast_le_iff fun n => ?_
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hH.analyticAt _),
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hH.analyticAt _)]
  have hfun : riemannHeat s = fun w => riemannHeat s (-w) :=
    funext fun w => (riemannHeat_neg hs w).symm
  have key : ∀ i w, iteratedDeriv i (riemannHeat s) w =
      (-1) ^ i * iteratedDeriv i (riemannHeat s) (-w) := by
    intro i w
    conv_lhs => rw [hfun]
    rw [iteratedDeriv_comp_neg, smul_eq_mul]
  exact ⟨fun h i hi => by rw [key i z, h i hi, mul_zero],
    fun h i hi => by rw [key i (-z), neg_neg, h i hi, mul_zero]⟩

/-- Affine centering relates `zeroMult (riemannHeat 0) z` to `(analyticOrderAt xi (1/2 + iz)).toNat`. -/
theorem zeroMult_riemannHeat_zero_eq_xi_order (z : ℂ) :
    zeroMult (riemannHeat 0) z = (analyticOrderAt xi ((1 / 2 : ℂ) + I * z)).toNat := by
  have hz : (((1 / 2 : ℂ) + I * z) - 1 / 2) * (-I) = z := by
    ring_nf; rw [I_sq]; ring
  rw [DeBruijn.riemannHeat_zero_eq_XiC, zeroMult, ← analyticOrderAt_XiC_centeredCoordinate, hz]

/-- **Exact unheated window accounting.** For every `T ∈ ℝ`, the nonreal zero count of `H_0` in
`|Re z| < T` is exactly twice `xiStripWindowOffLineOrder T`. -/
theorem xiWindowNonrealZeroCount_eq_two_mul_offLineOrder (T : ℝ) :
    xiWindowNonrealZeroCount T = 2 * xiStripWindowOffLineOrder T := by
  classical
  unfold xiWindowNonrealZeroCount
  set Z := (riemannHeat_zero_window_zeros_finite T).toFinset
  have hsplit := (Finset.sum_filter_add_sum_filter_not Z (fun z => 0 < z.re)
    (fun z => zeroMult (riemannHeat 0) z)).symm
  -- Reflection `z ↦ -z` equates `Z.filter (¬ 0 < ·.re)` with `Z.filter (0 < ·.re)`
  have hneg : ∑ z ∈ Z.filter (fun z => ¬ 0 < z.re), zeroMult (riemannHeat 0) z =
      ∑ z ∈ Z.filter (fun z => 0 < z.re), zeroMult (riemannHeat 0) z := by
    refine Finset.sum_bij (fun z _ => -z) (fun z hz => ?_) (fun a _ b _ h => neg_inj.mp h)
      (fun w hw => ?_) (fun z _ => (zeroMult_riemannHeat_neg le_rfl z).symm)
    · obtain ⟨hzZ, hle⟩ := Finset.mem_filter.mp hz
      obtain ⟨hz0, hzim, hzre⟩ := (Set.Finite.mem_toFinset _).mp hzZ
      have hlt : z.re < 0 := lt_of_le_of_ne (not_lt.mp hle) (re_ne_zero_of_riemannHeat_zero hz0)
      refine Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [riemannHeat_neg le_rfl, hz0]
      · simp [hzim]
      · simpa using hzre
      · simp; linarith
    · obtain ⟨hwZ, hwpos⟩ := Finset.mem_filter.mp hw
      obtain ⟨hw0, hwim, hwre⟩ := (Set.Finite.mem_toFinset _).mp hwZ
      refine ⟨-w, Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr ⟨?_, ?_, ?_⟩, ?_⟩,
        neg_neg w⟩
      · rw [riemannHeat_neg le_rfl, hw0]
      · simp [hwim]
      · simpa using hwre
      · simp; linarith
  -- Centering `z ↦ 1/2 + I * z` equates `Z.filter (0 < ·.re)` with off-line `stripZeros T`
  have hpos : ∑ z ∈ Z.filter (fun z => 0 < z.re), zeroMult (riemannHeat 0) z =
      xiStripWindowOffLineOrder T := by
    unfold xiStripWindowOffLineOrder
    refine Finset.sum_bij (fun z _ => (1 / 2 : ℂ) + I * z) (fun z hz => ?_)
      (fun a _ b _ h => mul_left_cancel₀ I_ne_zero (add_left_cancel h))
      (fun ρ hρ => ?_) (fun z _ => zeroMult_riemannHeat_zero_eq_xi_order z)
    · obtain ⟨hzZ, hzpos⟩ := Finset.mem_filter.mp hz
      obtain ⟨hz0, hzim, hzre⟩ := (Set.Finite.mem_toFinset _).mp hzZ
      have him_lt := abs_lt.mp (abs_im_lt_half_of_riemannHeat_zero hz0)
      rw [riemannHeat_zero] at hz0
      rw [abs_of_pos hzpos] at hzre
      refine Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr ⟨⟨?_, ?_, ?_, ?_⟩, hz0⟩, ?_⟩
      · simp; linarith
      · simp; linarith
      · simp [hzpos.le]
      · simp [hzre]
      · simp [hzim]
    · obtain ⟨hρS, hρne⟩ := Finset.mem_filter.mp hρ
      have hρpos := im_pos_of_mem_stripZeros hρS
      obtain ⟨⟨h0, h1, _, hltT⟩, hxi⟩ := (Set.Finite.mem_toFinset _).mp hρS
      refine ⟨(ρ - 1 / 2) * (-I), Finset.mem_filter.mpr
        ⟨(Set.Finite.mem_toFinset _).mpr ⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
      · rw [riemannHeat_zero, show (1 / 2 : ℂ) + I * ((ρ - 1 / 2) * (-I)) = ρ by
          ring_nf; rw [I_sq]; ring]
        exact hxi
      · simp; intro h; apply hρne; linarith
      · simp [abs_of_pos hρpos, hltT]
      · simp [hρpos]
      · ring_nf; rw [I_sq]; ring
  rw [hsplit, hneg, hpos, two_mul]

/-- For every `T ∈ ℝ`, `xiWindowNonrealZeroCount T ≤ 2 * xiHorizontalCollisionCharge T`. -/
theorem xiWindowNonrealZeroCount_le_two_mul_collisionCharge (T : ℝ) :
    xiWindowNonrealZeroCount T ≤ 2 * xiHorizontalCollisionCharge T := by
  rw [xiWindowNonrealZeroCount_eq_two_mul_offLineOrder]
  exact Nat.mul_le_mul_left 2 (xiStripWindowOffLineOrder_le_horizontalCollisionCharge T)

/-- Under minimal horizontal off-line fibres (`m_ρ = 1` and `H(Im ρ) = 2` at every off-line zero),
`O(U) = xiStripWindowOffLineOrder U` for every `U ∈ ℝ`. -/
theorem xiHorizontalCollisionCharge_eq_offLineOrder_of_minimal_fibres
    (hmin : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≠ 1 / 2 →
      (analyticOrderAt xi ρ).toNat = 1 ∧ xiHorizontalMultiplicity ρ.im = 2)
    (U : ℝ) :
    xiHorizontalCollisionCharge U = xiStripWindowOffLineOrder U := by
  classical
  unfold xiHorizontalCollisionCharge xiStripWindowOffLineOrder
  set S := (stripZeros_finite U).toFinset
  rw [← Finset.sum_filter_add_sum_filter_not S (fun ρ => ρ.re = 1 / 2)]
  have hcrit : ∑ ρ ∈ S.filter (fun ρ => ρ.re = 1 / 2),
      (analyticOrderAt xi ρ).toNat *
        (xiHorizontalMultiplicity ρ.im - (analyticOrderAt xi ρ).toNat) = 0 := by
    refine Finset.sum_eq_zero fun ρ hρ => ?_
    obtain ⟨hρS, hρre⟩ := Finset.mem_filter.mp hρ
    rw [horizontalMultiplicity_sub_order_eq_sum_same_im_erase hρS]
    suffices ((S.filter (fun z => z.im = ρ.im)).erase ρ) = ∅ by rw [this]; simp
    refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨hzne, hzF⟩ := Finset.mem_erase.mp hz
    obtain ⟨hzS, hzim⟩ := Finset.mem_filter.mp hzF
    have hz_off : z.re ≠ 1 / 2 := fun hzre => hzne (Complex.ext (hzre.trans hρre.symm) hzim)
    have hxi_z : xi z = 0 := ((Set.Finite.mem_toFinset _).mp hzS).2
    have hxi_ρ : xi ρ = 0 := ((Set.Finite.mem_toFinset _).mp hρS).2
    have hH2 := (hmin z hxi_z hz_off).2
    -- `{z, lineReflect z, ρ}` are three distinct points in `stripHeightFinset z.im`, forcing `H ≥ 3`
    have hz_mem : z ∈ stripHeightFinset z.im := by
      obtain ⟨⟨h0, h1, _, _⟩, _⟩ := (Set.Finite.mem_toFinset _).mp hzS
      exact mem_stripHeightFinset.mpr ⟨h0, h1, rfl, hxi_z⟩
    have hzr_mem : lineReflect z ∈ stripHeightFinset z.im := by
      have hrS := lineReflect_mem_stripZeros ((Set.Finite.mem_toFinset _).mp hzS)
      exact mem_stripHeightFinset.mpr ⟨hrS.1.1, hrS.1.2.1, by simp [lineReflect], hrS.2⟩
    have hρ_mem : ρ ∈ stripHeightFinset z.im := by
      obtain ⟨⟨h0, h1, _, _⟩, _⟩ := (Set.Finite.mem_toFinset _).mp hρS
      exact mem_stripHeightFinset.mpr ⟨h0, h1, hzim.symm, hxi_ρ⟩
    have hne1 : z ≠ lineReflect z := fun h => by
      have := congrArg Complex.re h; simp [lineReflect] at this; exact hz_off (by linarith)
    have hne2 : lineReflect z ≠ ρ := fun h => by
      have := congrArg Complex.re h; simp [lineReflect, hρre] at this; exact hz_off (by linarith)
    have hsub3 : ({z, lineReflect z, ρ} : Finset ℂ) ⊆ stripHeightFinset z.im := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hz_mem
      · rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hzr_mem
        · rw [Finset.mem_singleton.mp hw]; exact hρ_mem
    have hge3 : 3 ≤ xiHorizontalMultiplicity z.im := by
      calc 3 = ∑ w ∈ ({z, lineReflect z, ρ} : Finset ℂ), 1 := by
            rw [Finset.sum_insert (by simp [hne1, hzne]),
              Finset.sum_insert (by simp [hne2]), Finset.sum_singleton]
            rfl
        _ ≤ ∑ w ∈ ({z, lineReflect z, ρ} : Finset ℂ), (analyticOrderAt xi w).toNat := by
            refine Finset.sum_le_sum fun w hw => ?_
            have hwxi := (mem_stripHeightFinset.mp (hsub3 hw)).2.2.2
            exact Nat.one_le_iff_ne_zero.mpr (xi_order_toNat_ne_zero hwxi)
        _ ≤ xiHorizontalMultiplicity z.im := Finset.sum_le_sum_of_subset hsub3
    omega
  rw [hcrit, zero_add]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  obtain ⟨hρS, hρne⟩ := Finset.mem_filter.mp hρ
  obtain ⟨hm1, hH2⟩ := hmin ρ ((Set.Finite.mem_toFinset _).mp hρS).2 hρne
  rw [hm1, hH2]

/-- **Minimal-fibre parity falsification.** If `Ξ` has finitely many nonreal zero copies and minimal
horizontal off-line fibres, then for *every* height function `f : ℝ → ℝ` (including
`f(t) = 2π e^{40/t} + C`), the literal unnormalized inequality `N(t) ≤ O(f(t))` holds for small
`t > 0` if and only if `RiemannHypothesis` holds. -/
theorem eventually_nonrealZeroCount_le_collisionCharge_iff_rh_of_minimal_fibres
    (hfin : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite)
    (hmin : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≠ 1 / 2 →
      (analyticOrderAt xi ρ).toNat = 1 ∧ xiHorizontalMultiplicity ρ.im = 2)
    (f : ℝ → ℝ) :
    (∀ᶠ t in 𝓝[>] (0 : ℝ), nonrealZeroCount t ≤ xiHorizontalCollisionCharge (f t)) ↔
      RiemannHypothesis := by
  classical
  constructor
  · intro hev
    obtain ⟨t, ⟨ht_le, ht_eq⟩, _⟩ :=
      ((hev.and (eventually_nonrealZeroCount_eq_of_finite hfin)).and self_mem_nhdsWithin).exists
    set E := hfin.toFinset.image xiSpectralPoint
    set T_max : ℝ := max (f t) 1 + ∑ e ∈ E, (|e.re| + 1)
    have hE_sub : E ⊆ (riemannHeat_zero_window_zeros_finite T_max).toFinset := by
      intro e he
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
      have hq_im : (xiSpectralPoint q).im ≠ 0 := (Set.Finite.mem_toFinset hfin).mp hq
      have hle_sum : |(xiSpectralPoint q).re| + 1 ≤ ∑ w ∈ E, (|w.re| + 1) :=
        Finset.single_le_sum (f := fun w : ℂ => |w.re| + 1) (fun _ _ => by positivity) he
      have hf1 : 0 < max (f t) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
      refine (Set.Finite.mem_toFinset _).mpr ⟨?_, hq_im, by dsimp only [T_max]; linarith⟩
      rw [DeBruijn.riemannHeat_zero_eq_XiC]
      exact XiC_xiSpectralPoint_eq_zero q
    have hZ_sub : (riemannHeat_zero_window_zeros_finite T_max).toFinset ⊆ E := by
      intro z hz
      obtain ⟨hz0, hzim, _⟩ := (Set.Finite.mem_toFinset _).mp hz
      set ρ : ℂ := (1 / 2 : ℂ) + I * z
      have hρ0 : xi ρ = 0 := by rwa [← riemannHeat_zero]
      set s : XiDivisorSupport := ⟨ρ, mem_xi_divisor_support_of_eq_zero hρ0⟩
      obtain ⟨q, hq⟩ := (xiZeroCopyLineReflectionIncidence_nonempty s)
      have hqs : q.1.1 = s := mem_xiZeroCopyFiber.mp (Finset.mem_product.mp hq).1
      have hsp : xiSpectralPoint q.1 = z := by
        simp only [xiSpectralPoint, hqs, s, ρ]
        ring_nf; rw [I_sq]; ring
      refine Finset.mem_image.mpr ⟨q.1, (Set.Finite.mem_toFinset hfin).mpr ?_, hsp⟩
      rw [Set.mem_setOf_eq, hsp]
      exact hzim
    have hcard : hfin.toFinset.card = 2 * xiStripWindowOffLineOrder T_max := by
      rw [card_nonrealCopies_eq_sum_zeroMult hfin]
      change ∑ e ∈ E, zeroMult (riemannHeat 0) e = 2 * xiStripWindowOffLineOrder T_max
      rw [Finset.Subset.antisymm hE_sub hZ_sub,
        ← xiWindowNonrealZeroCount, xiWindowNonrealZeroCount_eq_two_mul_offLineOrder]
    have hO_eq := xiHorizontalCollisionCharge_eq_offLineOrder_of_minimal_fibres hmin (f t)
    have hft_le : f t ≤ T_max := by
      have : 0 ≤ ∑ e ∈ E, (|e.re| + 1) := Finset.sum_nonneg fun _ _ => by positivity
      dsimp only [T_max]; linarith [le_max_left (f t) 1]
    have hoff_mono := xiStripWindowOffLineOrder_mono hft_le
    rw [ht_eq, hcard, hO_eq] at ht_le
    have hoff0 : xiStripWindowOffLineOrder T_max = 0 := by omega
    have hcard0 : hfin.toFinset.card = 0 := by rw [hcard, hoff0]
    refine riemannHypothesis_iff_eventually_nonrealZeroCount_eq_zero.mpr ?_
    filter_upwards [eventually_nonrealZeroCount_eq_of_finite hfin] with s hs
    rw [hs, hcard0]
  · intro hRH
    filter_upwards [riemannHypothesis_iff_eventually_nonrealZeroCount_eq_zero.mp hRH] with t ht
    rw [ht]
    exact Nat.zero_le _

/-! ## §2. Cubic Calogero–Moser inward-drift obstruction (`C = 0` fails) -/

/-- Shifted cubic `P_A(X) = ((X − A)² + 4)(X − (A + 1/2))` placing a conjugate pair on the window
boundary `|Re z| = A` and a real zero just outside at `A + 1/2`. -/
def inwardDriftCubic (A : ℝ) : ℝ[X] :=
  (X - C A) ^ 3 - C (1 / 2) * (X - C A) ^ 2 + C 4 * (X - C A) - C 2

theorem natDegree_inwardDriftCubic (A : ℝ) : (inwardDriftCubic A).natDegree = 3 := by
  have hexp : inwardDriftCubic A =
      X ^ 3 + C (-(3 * A + 1 / 2)) * X ^ 2 + C (3 * A ^ 2 + A + 4) * X +
        C (-(A ^ 3 + A ^ 2 / 2 + 4 * A + 2)) := by
    unfold inwardDriftCubic
    rw [show 3 * A ^ 2 + A + 4 = 3 * A ^ 2 + 2 * (1 / 2) * A + 4 by ring,
      show A ^ 3 + A ^ 2 / 2 + 4 * A + 2 = A ^ 3 + (1 / 2) * A ^ 2 + 4 * A + 2 by ring]
    simp only [map_neg, map_add, map_mul, map_pow, map_ofNat]
    ring
  rw [hexp]
  compute_degree!

theorem inwardDriftCubic_ne_zero (A : ℝ) : inwardDriftCubic A ≠ 0 := by
  intro h
  have := natDegree_inwardDriftCubic A
  rw [h, natDegree_zero] at this
  norm_num at this

theorem map_inwardDriftCubic (A : ℝ) :
    (inwardDriftCubic A).map Complex.ofRealHom =
      (X - C ((A : ℂ) + 2 * I)) * (X - C ((A : ℂ) - 2 * I)) *
        (X - C (((A + 1 / 2 : ℝ) : ℂ))) := by
  unfold inwardDriftCubic
  simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    map_X, map_C, Complex.ofRealHom_eq_coe, Complex.ofReal_ofNat, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_add]
  have hpair : (X - C ((A : ℂ) + 2 * I)) * (X - C ((A : ℂ) - 2 * I)) =
      (X - C (A : ℂ)) ^ 2 + C 4 := by
    have : (X - C ((A : ℂ) + 2 * I)) * (X - C ((A : ℂ) - 2 * I)) =
        ((X - C (A : ℂ)) - C (2 * I)) * ((X - C (A : ℂ)) + C (2 * I)) := by
      simp only [map_add, map_sub]; ring
    rw [this, show ((X - C (A : ℂ)) - C (2 * I)) * ((X - C (A : ℂ)) + C (2 * I)) =
      (X - C (A : ℂ)) ^ 2 - C ((2 * I) ^ 2) by rw [C_pow]; ring]
    rw [mul_pow, I_sq, show ((2 : ℂ) ^ 2 * -1) = -4 by norm_num, C_neg, sub_neg_eq_add]
  rw [hpair, show C ((A : ℂ) + 1 / 2) = C (A : ℂ) + C (1 / 2) by rw [map_add]]
  have h42 : (C (2 : ℂ) : ℂ[X]) = C 4 * C (1 / 2) := by rw [← map_mul]; norm_num
  rw [h42]
  ring

theorem polyHeat_quarter_inwardDriftCubic (A : ℝ) :
    polyHeat (1 / 4) (inwardDriftCubic A) =
      (X - C A) ^ 3 - C (1 / 2) * (X - C A) ^ 2 + C (5 / 2) * (X - C A) - C (7 / 4) := by
  have hd2 : derivative^[2] (inwardDriftCubic A) = C 6 * (X - C A) - C 1 := by
    have hexp : inwardDriftCubic A =
        X ^ 3 + C (-(3 * A + 1 / 2)) * X ^ 2 + C (3 * A ^ 2 + A + 4) * X +
          C (-(A ^ 3 + A ^ 2 / 2 + 4 * A + 2)) := by
      unfold inwardDriftCubic
      rw [show 3 * A ^ 2 + A + 4 = 3 * A ^ 2 + 2 * (1 / 2) * A + 4 by ring,
        show A ^ 3 + A ^ 2 / 2 + 4 * A + 2 = A ^ 3 + (1 / 2) * A ^ 2 + 4 * A + 2 by ring]
      simp only [map_neg, map_add, map_mul, map_pow, map_ofNat]
      ring
    rw [hexp, Function.iterate_succ_apply', Function.iterate_one]
    simp only [derivative_add, derivative_mul, derivative_pow, derivative_X, derivative_C,
      Nat.cast_ofNat, mul_one, zero_mul, zero_add, add_zero, pow_one,
      show (3 - 1 : ℕ) = 2 by rfl, show (2 - 1 : ℕ) = 1 by rfl]
    ext n; simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X, coeff_C]; split_ifs <;> ring
  have hd4 : ∀ k ≥ 2, derivative^[2 * k] (inwardDriftCubic A) = 0 := fun k hk =>
    iterate_derivative_eq_zero (by rw [natDegree_inwardDriftCubic]; omega)
  unfold polyHeat
  rw [natDegree_inwardDriftCubic, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    hd4 2 (by omega), hd4 3 (by omega)]
  simp only [zero_add, add_zero, mul_zero, Function.iterate_zero_apply, pow_zero,
    Nat.factorial_zero, Nat.cast_one, div_one, C_1, one_mul, mul_one, pow_one,
    Nat.factorial_one, hd2]
  unfold inwardDriftCubic
  rw [← C_1]
  ext n; simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_C]; split_ifs <;> ring

/-- **Calogero–Moser inward-drift theorem.** For every height `A > 1/4`, `inwardDriftCubic A` has
`0` nonreal roots in the open strip `|Re z| < A`, whereas `polyHeat (1/4) (inwardDriftCubic A)` has
`2` nonreal roots strictly inside `|Re z| < A`. Thus the unbuffered (`C = 0`) windowed nonreal root
count is *not* monotone nonincreasing under `polyHeat`. -/
theorem exists_polyHeat_nonreal_root_inward_drift {A : ℝ} (hA : 1 / 4 < A) :
    Multiset.card (((inwardDriftCubic A).map Complex.ofRealHom).roots.filter
      (fun z => z.im ≠ 0 ∧ |z.re| < A)) = 0 ∧
    Multiset.card (((polyHeat (1 / 4) (inwardDriftCubic A)).map Complex.ofRealHom).roots.filter
      (fun z => z.im ≠ 0 ∧ |z.re| < A)) = 2 := by
  classical
  constructor
  · -- At `t = 0`, complex roots are `A + 2i`, `A - 2i`, `A + 1/2`, none with `Im ≠ 0 ∧ |Re| < A`
    rw [map_inwardDriftCubic]
    have h12 : (X - C ((A : ℂ) + 2 * I)) * (X - C ((A : ℂ) - 2 * I)) ≠ 0 :=
      mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
    have h3 : (X - C (((A + 1 / 2 : ℝ) : ℂ))) ≠ 0 := X_sub_C_ne_zero _
    rw [roots_mul (mul_ne_zero h12 h3), roots_mul h12, roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
    have hA0 : 0 < A := by linarith
    have hf1 : ¬ (((A : ℂ) + 2 * I).im ≠ 0 ∧ |((A : ℂ) + 2 * I).re| < A) := by
      simp [abs_of_pos hA0]
    have hf2 : ¬ (((A : ℂ) - 2 * I).im ≠ 0 ∧ |((A : ℂ) - 2 * I).re| < A) := by
      simp [abs_of_pos hA0]
    have hf3 : ¬ ((((A + 1 / 2 : ℝ) : ℂ)).im ≠ 0 ∧ |(((A + 1 / 2 : ℝ) : ℂ)).re| < A) := by
      simp
    rw [Multiset.filter_add, Multiset.filter_add, Multiset.filter_singleton,
      Multiset.filter_singleton, Multiset.filter_singleton, if_neg hf1, if_neg hf2, if_neg hf3,
      Multiset.empty_eq_zero, add_zero, add_zero, Multiset.card_zero]
  · -- At `t = 1/4`, locate the unique real shift root `w₁ ∈ (1/2, 1)` by IVT and factor explicitly
    set g : ℝ → ℝ := fun w => w ^ 3 - (1 / 2) * w ^ 2 + (5 / 2) * w - 7 / 4
    have hg_cont : ContinuousOn g (Icc (1 / 2) 1) := by fun_prop
    have hg_half : g (1 / 2) = -1 / 2 := by simp only [g]; norm_num
    have hg_one : g 1 = 5 / 4 := by simp only [g]; norm_num
    have h0_mem : (0 : ℝ) ∈ Icc (g (1 / 2)) (g 1) := by rw [hg_half, hg_one]; constructor <;> norm_num
    obtain ⟨w₁, hw₁I, hw₁0⟩ := intermediate_value_Icc (by norm_num : (1 / 2 : ℝ) ≤ 1) hg_cont h0_mem
    have hw₁_gt : 1 / 2 < w₁ := lt_of_le_of_ne hw₁I.1 fun h => by
      rw [← h, hg_half] at hw₁0; norm_num at hw₁0
    have hw₁_lt : w₁ < 1 := lt_of_le_of_ne hw₁I.2 fun h => by
      rw [h, hg_one] at hw₁0; norm_num at hw₁0
    set b : ℝ := w₁ - 1 / 2
    set c : ℝ := w₁ ^ 2 - (1 / 2) * w₁ + 5 / 2
    have hdisc_pos : 0 < 4 * c - b ^ 2 := by
      dsimp only [b, c]
      nlinarith [sq_nonneg (w₁ - 1 / 6)]
    set v : ℝ := Real.sqrt (4 * c - b ^ 2) / 2
    have hv_pos : 0 < v := div_pos (Real.sqrt_pos.mpr hdisc_pos) two_pos
    have hv_sq : v ^ 2 = c - b ^ 2 / 4 := by
      dsimp only [v]; rw [div_pow, Real.sq_sqrt hdisc_pos.le]; ring
    set u : ℝ := -b / 2
    have hu_neg : u < 0 := by dsimp only [u, b]; linarith
    have hu_gt : -(1 / 4) < u := by dsimp only [u, b]; linarith
    set z₁ : ℂ := ((A + w₁ : ℝ) : ℂ)
    set z₂ : ℂ := ((A + u : ℝ) : ℂ) + (v : ℂ) * I
    set z₃ : ℂ := ((A + u : ℝ) : ℂ) - (v : ℂ) * I
    have hfac : ((polyHeat (1 / 4) (inwardDriftCubic A)).map Complex.ofRealHom) =
        (X - C z₁) * (X - C z₂) * (X - C z₃) := by
      rw [polyHeat_quarter_inwardDriftCubic]
      simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
        map_X, map_C, Complex.ofRealHom_eq_coe]
      have hw₁_eq : w₁ * c = 7 / 4 := by dsimp only [c]; dsimp only [g] at hw₁0; linarith
      have hquad : (X - C z₂) * (X - C z₃) =
          (X - C (A : ℂ)) ^ 2 + C (b : ℂ) * (X - C (A : ℂ)) + C (c : ℂ) := by
        have h23 : (X - C z₂) * (X - C z₃) =
            ((X - C (A : ℂ) - C (u : ℂ)) - C ((v : ℂ) * I)) *
              ((X - C (A : ℂ) - C (u : ℂ)) + C ((v : ℂ) * I)) := by
          dsimp only [z₂, z₃]; simp only [Complex.ofReal_add, map_add, map_sub]; ring
        rw [h23, show ((X - C (A : ℂ) - C (u : ℂ)) - C ((v : ℂ) * I)) *
            ((X - C (A : ℂ) - C (u : ℂ)) + C ((v : ℂ) * I)) =
            (X - C (A : ℂ) - C (u : ℂ)) ^ 2 - C (((v : ℂ) * I) ^ 2) by rw [C_pow]; ring]
        have hvI : ((v : ℂ) * I) ^ 2 = ((-(v ^ 2) : ℝ) : ℂ) := by
          rw [mul_pow, I_sq]; push_cast; ring
        have hub : -2 * u = b := by dsimp only [u]; ring
        have huc : u ^ 2 + v ^ 2 = c := by rw [hv_sq]; dsimp only [u]; ring
        rw [hvI, ← huc, ← hub]
        push_cast; simp only [map_neg, map_add, map_mul, map_pow, map_ofNat]; ring
      rw [mul_assoc, hquad]
      have hz1 : X - C z₁ = (X - C (A : ℂ)) - C (w₁ : ℂ) := by
        dsimp only [z₁]; simp only [Complex.ofReal_add, map_add]; ring
      rw [hz1]
      have hb_eq : b - w₁ = -(1 / 2 : ℝ) := by dsimp only [b]; ring
      have hc_eq : c - w₁ * b = (5 / 2 : ℝ) := by dsimp only [b, c]; ring
      have hhalf' : (C ((1 / 2 : ℝ) : ℂ) : ℂ[X]) = C ((w₁ - b : ℝ) : ℂ) := by
        congr 2; linarith
      have h52' : (C ((5 / 2 : ℝ) : ℂ) : ℂ[X]) = C ((c - w₁ * b : ℝ) : ℂ) := by
        congr 2; linarith
      have h74' : (C ((7 / 4 : ℝ) : ℂ) : ℂ[X]) = C ((w₁ * c : ℝ) : ℂ) := by
        congr 2; linarith
      rw [hhalf', h52', h74']
      simp only [Complex.ofReal_sub, Complex.ofReal_mul, map_sub, map_mul]
      ring
    rw [hfac]
    have h12 : (X - C z₁) * (X - C z₂) ≠ 0 := mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
    have h3 : (X - C z₃) ≠ 0 := X_sub_C_ne_zero _
    rw [roots_mul (mul_ne_zero h12 h3), roots_mul h12, roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
    have hAu_pos : 0 < A + u := by linarith
    have hAu_lt : A + u < A := by linarith
    have ht1 : ¬ (z₁.im ≠ 0 ∧ |z₁.re| < A) := by simp [z₁]
    have ht2 : z₂.im ≠ 0 ∧ |z₂.re| < A := by
      simp [z₂, hv_pos.ne', abs_of_pos hAu_pos, hAu_lt]
    have ht3 : z₃.im ≠ 0 ∧ |z₃.re| < A := by
      simp [z₃, hv_pos.ne', abs_of_pos hAu_pos, hAu_lt]
    rw [Multiset.filter_add, Multiset.filter_add, Multiset.filter_singleton,
      Multiset.filter_singleton, Multiset.filter_singleton, if_neg ht1, if_pos ht2, if_pos ht3,
      Multiset.card_add, Multiset.card_add, Multiset.card_empty, Multiset.card_singleton,
      Multiset.card_singleton]

/-! ## §3. Forward real-zero stability at `t ≥ 0` and moving-barrier windowed descent -/

/-- Unified right-sided locally uniform convergence `riemannHeat (max s 0) → riemannHeat t` on
`𝓝[>] t` for every `t ≥ 0` (covering both `t = 0` and `t > 0`). -/
theorem tendstoLocallyUniformly_riemannHeat_nhdsGT {t : ℝ} (ht : 0 ≤ t) :
    TendstoLocallyUniformly (fun s : ℝ => riemannHeat (max s 0)) (riemannHeat t) (𝓝[>] t) := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · exact tendstoLocallyUniformly_riemannHeat_max_zero
  · intro u hu x
    obtain ⟨V, hV, hev⟩ := tendstoLocallyUniformly_riemannHeat_nhds htpos u hu x
    refine ⟨V, hV, ?_⟩
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hsgt y hy
    have hs0 : 0 ≤ s := htpos.le.trans (Set.mem_Ioi.mp hsgt).le
    simpa [max_eq_left hs0] using hs y hy

/-- Right-sided disc-count stability at any `t ≥ 0` (including `t = 0`). -/
theorem eventually_zeroSumBall_riemannHeat_eq_nhdsGT {t : ℝ} (ht : 0 ≤ t) (z₀ : ℂ) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ →
      (∀ w ∈ sphere z₀ r, riemannHeat t w ≠ 0) ∧
      zeroSumBall (riemannHeat t) z₀ r = (zeroMult (riemannHeat t) z₀ : ℂ) ∧
      ∀ᶠ s in 𝓝[>] t, zeroSumBall (riemannHeat s) z₀ r = (zeroMult (riemannHeat t) z₀ : ℂ) ∧
        ∀ w ∈ sphere z₀ r, riemannHeat s w ≠ 0 := by
  obtain ⟨r₀, hr₀, h⟩ := exists_radius_zeroSumBall_riemannHeat_eq ht z₀
  refine ⟨r₀, hr₀, fun r hr hrr => ?_⟩
  obtain ⟨hsph, hcount⟩ := h r hr hrr
  refine ⟨hsph, hcount, ?_⟩
  set F : ℝ → ℂ → ℂ := fun s => riemannHeat (max s 0)
  have hF : ∀ s, Differentiable ℂ (F s) := fun _ => differentiable_riemannHeat (le_max_right _ _)
  have hdiff := differentiable_riemannHeat ht
  have hconv := tendstoLocallyUniformly_riemannHeat_nhdsGT ht
  have h1 := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly hF hdiff hconv hr
    (by linarith : r < 2 * r) hsph
  have h2 := eventually_ne_zero_on_sphere hdiff.continuous hconv hr.le hsph
  filter_upwards [h1, h2, self_mem_nhdsWithin] with s hs1 hs2 hsgt
  have hs0 : 0 ≤ s := ht.trans (Set.mem_Ioi.mp hsgt).le
  simp only [F, max_eq_left hs0] at hs1 hs2
  exact ⟨by rw [hs1, hcount], hs2⟩

/-- **Real zeros stay real forward from `t ≥ 0` (including `t = 0`).** Around any real point `x₀`,
there is `r₀ > 0` such that for every `0 < r ≤ r₀` there is `δ > 0` with: for `t < s < t + δ`,
every zero of `H_s` in `ball x₀ r` is real. -/
theorem exists_ball_real_zeros_forward_nonneg {t : ℝ} (ht : 0 ≤ t) (x₀ : ℝ) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∃ δ > 0, ∀ s, t < s → s < t + δ →
      ∀ w ∈ ball (x₀ : ℂ) r, riemannHeat s w = 0 → w.im = 0 := by
  classical
  rcases eq_or_lt_of_le ht with rfl | htpos
  · obtain ⟨r₀, hr₀, hstable⟩ := eventually_zeroSumBall_riemannHeat_eq_nhdsGT le_rfl (x₀ : ℂ)
    refine ⟨r₀, hr₀, fun r hr hrr₀ => ?_⟩
    obtain ⟨hsph, hcount, hev⟩ := hstable r hr hrr₀
    set k := zeroMult (riemannHeat 0) x₀ with hk
    have han : AnalyticAt ℂ (riemannHeat 0) x₀ := (differentiable_riemannHeat le_rfl).analyticAt _
    have hord : analyticOrderAt (riemannHeat 0) x₀ = (k : ℕ∞) := by
      rw [hk, zeroMult, ENat.coe_toNat (analyticOrderAt_riemannHeat_ne_top le_rfl _)]
    obtain ⟨hvan, hka⟩ := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero han).mp hord
    obtain ⟨S, hS, q₁, hq₁, hreal⟩ := exists_real_zeros_forward le_rfl hvan hka
    obtain ⟨δ₁, hδ₁, hδ₁ev⟩ := Metric.mem_nhdsWithin_iff.mp hev
    set q₂ := min q₁ (r / (2 * S))
    have hq₂ : 0 < q₂ := lt_min hq₁ (by positivity)
    refine ⟨min δ₁ (q₂ ^ 2), lt_min hδ₁ (by positivity), fun s hts hst w hw hw0 => ?_⟩
    rw [zero_add] at hst
    have hsq : s < q₂ ^ 2 := lt_of_lt_of_le hst (min_le_right _ _)
    have hs_mem : s ∈ ball (0 : ℝ) δ₁ ∩ Ioi 0 :=
      ⟨by rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hts]; exact lt_of_lt_of_le hst (min_le_left _ _),
        hts⟩
    obtain ⟨hcs, hsph_s⟩ := hδ₁ev hs_mem
    set q := Real.sqrt s
    have hq : 0 < q := Real.sqrt_pos.mpr hts
    have hqq : q ≤ q₂ := (Real.sqrt_le_left (by positivity)).mpr hsq.le
    have hsq' : (0 : ℝ) + q ^ 2 = s := by rw [zero_add, Real.sq_sqrt hts.le]
    obtain ⟨Y, hYcard, hY⟩ := hreal q hq (hqq.trans (min_le_left _ _))
    rw [hsq'] at hY
    have hqS : q * S ≤ r / 2 := by
      have := hqq.trans (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    have hs0 : 0 ≤ s := hts.le
    obtain ⟨Z, hZball, hZzero, hsum⟩ := exists_zeroSet_zeroSumBall hr (by linarith : r < 2 * r)
      isOpen_univ (subset_univ _) (differentiable_riemannHeat hs0).differentiableOn hsph_s
    rw [hcs] at hsum
    have hsumN : ∑ z ∈ Z, zeroMult (riemannHeat s) z = k := by
      have : ((∑ z ∈ Z, zeroMult (riemannHeat s) z : ℕ) : ℂ) = (k : ℂ) := by
        push_cast; exact hsum.symm
      exact_mod_cast this
    set Y' := Y.image (fun y : ℝ => (y : ℂ))
    have hY'card : Y'.card = k := by
      rw [Finset.card_image_of_injective _ Complex.ofReal_injective, hYcard]
    have hY'Z : Y' ⊆ Z := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hyd, hy0⟩ := hY y hy
      have hyb : (y : ℂ) ∈ ball (x₀ : ℂ) r := by
        rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        linarith
      exact (hZzero _ hyb).mp hy0
    have hsplit := Finset.sum_sdiff hY'Z (f := fun z => zeroMult (riemannHeat s) z)
    have hY'sum : k ≤ ∑ z ∈ Y', zeroMult (riemannHeat s) z := by
      rw [← hY'card, Finset.card_eq_sum_ones]
      refine Finset.sum_le_sum fun z hz => one_le_zeroMult_riemannHeat hs0 ?_
      exact (hZzero z (hZball z (hY'Z hz))).mpr (hY'Z hz)
    have hrest : Z \ Y' = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
      have h1 : 1 ≤ zeroMult (riemannHeat s) z :=
        one_le_zeroMult_riemannHeat hs0 ((hZzero z (hZball z (Finset.sdiff_subset hz))).mpr
          (Finset.sdiff_subset hz))
      have h2 := Finset.single_le_sum (f := fun z => zeroMult (riemannHeat s) z)
        (fun _ _ => Nat.zero_le _) hz
      omega
    have hwZ : w ∈ Z := (hZzero w hw).mp hw0
    have hwY : w ∈ Y' := by
      by_contra hn
      have : w ∈ Z \ Y' := Finset.mem_sdiff.mpr ⟨hwZ, hn⟩
      rw [hrest] at this
      exact Finset.notMem_empty _ this
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hwY
    exact Complex.ofReal_im y
  · exact exists_ball_real_zeros_forward htpos x₀

/-- Interval-interior real induction on `[a, b]`: right-local nonincrease on `[a, b)` and left-local
lower semicontinuity on `(a, b]` imply `N b ≤ N a` without evaluating `N` outside `[a, b]`. -/
private theorem le_of_local_right_Ico_and_lsc_Ioc {N : ℝ → ℕ} {a b : ℝ} (hab : a ≤ b)
    (hright : ∀ c ∈ Ico a b, ∃ δ > 0, ∀ s ∈ Ioc c b, s < c + δ → N s ≤ N c)
    (hlsc : ∀ c ∈ Ioc a b, ∃ δ > 0, ∀ s ∈ Ico a c, c - δ < s → N c ≤ N s) :
    N b ≤ N a := by
  set S := {t ∈ Icc a b | ∀ u ∈ Icc a t, N u ≤ N a}
  have haS : a ∈ S := ⟨⟨le_rfl, hab⟩, fun u hu => by rw [le_antisymm hu.2 hu.1]⟩
  have hbdd : BddAbove S := ⟨b, fun t ht => ht.1.2⟩
  set c := sSup S
  have hac : a ≤ c := le_csSup hbdd haS
  have hcb : c ≤ b := csSup_le ⟨a, haS⟩ fun t ht => ht.1.2
  have hbelow : ∀ u ∈ Ico a c, N u ≤ N a := fun u hu => by
    obtain ⟨t, htS, hut⟩ := exists_lt_of_lt_csSup ⟨a, haS⟩ hu.2
    exact htS.2 u ⟨hu.1, hut.le⟩
  have hcS : c ∈ S := by
    refine ⟨⟨hac, hcb⟩, fun u hu => ?_⟩
    rcases lt_or_eq_of_le hu.2 with hlt | rfl
    · exact hbelow u ⟨hu.1, hlt⟩
    · rcases lt_or_eq_of_le hac with hac' | heq
      · obtain ⟨δ, hδ, hl⟩ := hlsc c ⟨hac', hcb⟩
        set u' := max a (c - δ / 2)
        have hu'I : u' ∈ Ico a c := ⟨le_max_left _ _, max_lt hac' (by linarith)⟩
        exact (hl u' hu'I (lt_of_lt_of_le (by linarith) (le_max_right _ _))).trans (hbelow u' hu'I)
      · rw [← heq]
  rcases lt_or_eq_of_le hcb with hlt | heq
  · exfalso
    obtain ⟨δ, hδ, hr⟩ := hright c ⟨hac, hlt⟩
    set c' := min b (c + δ / 2)
    have hcc' : c < c' := lt_min hlt (by linarith)
    have hc'S : c' ∈ S := by
      refine ⟨⟨hac.trans hcc'.le, min_le_left _ _⟩, fun u hu => ?_⟩
      rcases le_or_gt u c with huc | huc
      · exact hcS.2 u ⟨hu.1, huc⟩
      · have hu2 : u < c + δ := lt_of_le_of_lt hu.2 (lt_of_le_of_lt (min_le_right _ _) (by linarith))
        exact (hr u ⟨huc, hu.2.trans (min_le_left _ _)⟩ hu2).trans (hcS.2 c ⟨hac, le_rfl⟩)
    exact not_lt.mpr (le_csSup hbdd hc'S) hcc'
  · rw [← heq]
    exact hcS.2 c ⟨hac, le_rfl⟩

/-- Nonreal zero count of `H_s` (`s ≥ 0`) inside the horizontal window `|Re z| < X`. -/
def riemannHeatWindowNonrealCount (s X : ℝ) : ℕ :=
  if hs : 0 < s then
    ∑ z ∈ (riemannHeat_nonreal_zeros_finite hs).toFinset.filter (fun z => |z.re| < X),
      zeroMult (riemannHeat s) z
  else if s = 0 then
    xiWindowNonrealZeroCount X
  else 0

theorem riemannHeatWindowNonrealCount_zero (X : ℝ) :
    riemannHeatWindowNonrealCount 0 X = xiWindowNonrealZeroCount X := by
  simp [riemannHeatWindowNonrealCount]

theorem riemannHeatWindowNonrealCount_pos {s : ℝ} (hs : 0 < s) (X : ℝ) :
    riemannHeatWindowNonrealCount s X =
      ∑ z ∈ (riemannHeat_nonreal_zeros_finite hs).toFinset.filter (fun z => |z.re| < X),
        zeroMult (riemannHeat s) z :=
  dif_pos hs

/-- Above the Ki–Kim–Lee horizon `2π e^{40/t}` (`0 < t ≤ 1/8`), the windowed nonreal count equals
the full nonreal zero count `N(t)`. -/
theorem riemannHeatWindowNonrealCount_eq_nonrealZeroCount {t X : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hX : 2 * Real.pi * Real.exp (40 / t) ≤ X) :
    riemannHeatWindowNonrealCount t X = nonrealZeroCount t := by
  rw [riemannHeatWindowNonrealCount_pos ht, nonrealZeroCount_eq ht]
  congr 1
  refine Finset.filter_eq_self.mpr fun z hz => ?_
  obtain ⟨hz0, hzim⟩ := (Set.Finite.mem_toFinset _).mp hz
  by_contra hge
  exact hzim (riemannHeat_zeros_real_of_le_re ht ht8 hz0 (hX.trans (not_lt.mp hge)))

/-- **Moving-barrier windowed descent theorem.** Let `0 < t ≤ 1/8` and let `R : ℝ → ℝ` be continuous
on `[0, t]` with `2π e^{40/t} ≤ R(t)` such that for every `s ∈ [0, t]`, `H_s` has no nonreal zero
on the moving vertical boundary `|Re z| = R(s)`. Then
`N(t) ≤ xiWindowNonrealZeroCount (R 0) ≤ 2 * O(R 0)`. -/
theorem nonrealZeroCount_le_two_mul_collisionCharge_of_barrier {t : ℝ} (ht : 0 < t)
    (ht8 : t ≤ 1 / 8) {R : ℝ → ℝ} (hRcont : ContinuousOn R (Icc 0 t))
    (hRkkl : 2 * Real.pi * Real.exp (40 / t) ≤ R t)
    (hbarrier : ∀ s ∈ Icc 0 t, ∀ z : ℂ, riemannHeat s z = 0 → |z.re| = R s → z.im = 0) :
    nonrealZeroCount t ≤ xiWindowNonrealZeroCount (R 0) ∧
      nonrealZeroCount t ≤ 2 * xiHorizontalCollisionCharge (R 0) := by
  classical
  suffices hwin : nonrealZeroCount t ≤ xiWindowNonrealZeroCount (R 0) by
    exact ⟨hwin, hwin.trans (xiWindowNonrealZeroCount_le_two_mul_collisionCharge (R 0))⟩
  rw [← riemannHeatWindowNonrealCount_eq_nonrealZeroCount ht ht8 hRkkl,
    ← riemannHeatWindowNonrealCount_zero (R 0)]
  refine le_of_local_right_Ico_and_lsc_Ioc (N := fun s => riemannHeatWindowNonrealCount s (R s))
    ht.le (fun s₀ hs₀ => ?_) (fun s₁ hs₁ => ?_)
  · -- Right-local nonincrease on `[0, t)`
    have hs₀_nn : 0 ≤ s₀ := hs₀.1
    set M₀ : ℝ := max (R s₀) 0 + 2
    have hM₀_pos : 0 < M₀ := by dsimp only [M₀]; positivity
    have han : AnalyticOnNhd ℂ (riemannHeat s₀) (closedBall 0 (M₀ + 2)) := fun z _ =>
      (differentiable_riemannHeat hs₀_nn).analyticAt z
    have hfin := finite_zeros_closedBall han (fun z _ h =>
      analyticOrderAt_riemannHeat_ne_top hs₀_nn z (analyticOrderAt_eq_top.mpr h))
    set E_all := hfin.toFinset
    set E_in := E_all.filter (fun e => e.im ≠ 0 ∧ |e.re| < R s₀)
    set E_out := E_all.filter (fun e => e.im ≠ 0 ∧ R s₀ < |e.re|)
    -- Gap `η > 0` separating `E_out` from `|Re z| ≤ R s₀`
    obtain ⟨η, hη_pos, hη_le1, hη_out⟩ :
        ∃ η > 0, η ≤ 1 ∧ ∀ e ∈ E_out, R s₀ + 3 * η ≤ |e.re| := by
      rcases E_out.eq_empty_or_nonempty with hemp | hne
      · exact ⟨1, one_pos, le_rfl, fun e he => by rw [hemp] at he; simp at he⟩
      · set g := E_out.inf' hne (fun e => (|e.re| - R s₀) / 3)
        have hg_pos : 0 < g := (Finset.lt_inf'_iff hne).mpr fun e he => by
          have := (Finset.mem_filter.mp he).2.2; linarith
        refine ⟨min 1 g, lt_min one_pos hg_pos, min_le_left _ _, fun e he => ?_⟩
        have h1 : min 1 g ≤ (|e.re| - R s₀) / 3 :=
          (min_le_right 1 g).trans (Finset.inf'_le _ he)
        linarith
    choose ρ₀ hρ₀ hρ₀prop using fun e => eventually_zeroSumBall_riemannHeat_eq_nhdsGT hs₀_nn e
    choose ρ₁ hρ₁ hρ₁prop using fun e : ℂ => exists_ball_real_zeros_forward_nonneg hs₀_nn e.re
    obtain ⟨d, hd, hdsep⟩ := exists_pos_sep E_all
    set A_rad : ℂ → ℝ := fun e => min (min (ρ₀ e) (ρ₁ e)) (min (d / 3) η)
    set r : ℂ → ℝ := fun e => if e.im = 0 then A_rad e else min (A_rad e) (|e.im| / 2)
    have hrA : ∀ e, r e ≤ A_rad e := fun e => by
      simp only [r]; split_ifs; exact le_rfl; exact min_le_left _ _
    have hApos : ∀ e, 0 < A_rad e := fun e =>
      lt_min (lt_min (hρ₀ e) (hρ₁ e)) (lt_min (by positivity) hη_pos)
    have hrpos : ∀ e, 0 < r e := fun e => by
      simp only [r]; split_ifs with h
      · exact hApos e
      · exact lt_min (hApos e) (div_pos (abs_pos.mpr h) two_pos)
    have hr₀ : ∀ e, r e ≤ ρ₀ e := fun e => (hrA e).trans ((min_le_left _ _).trans (min_le_left _ _))
    have hr₁ : ∀ e, r e ≤ ρ₁ e := fun e => (hrA e).trans ((min_le_left _ _).trans (min_le_right _ _))
    have hrd : ∀ e, r e ≤ d / 3 := fun e => (hrA e).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hrη : ∀ e, r e ≤ η := fun e => (hrA e).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hdisj : ∀ e ∈ E_all, ∀ e' ∈ E_all, e ≠ e' → Disjoint (ball e (r e)) (ball e' (r e')) := by
      intro e he e' he' hne
      refine Set.disjoint_left.mpr fun w hw hw' => ?_
      have h1 := hdsep e he e' he' hne
      have h2 := dist_triangle e w e'
      rw [mem_ball] at hw hw'; rw [dist_comm] at hw
      linarith [hrd e, hrd e']
    -- Compact remainder `K_rem = K_box \ ⋃_{e ∈ E_all} ball e (r e)` is zero-free for `H_{s₀}`
    set K_box : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) ''
      (Icc (-M₀) M₀ ×ˢ Icc (-1) 1)
    have hK_box_comp : IsCompact K_box :=
      (isCompact_Icc.prod isCompact_Icc).image
        ((Complex.continuous_ofReal.comp continuous_fst).add
          ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
    set U_balls : Set ℂ := ⋃ e ∈ E_all, ball e (r e)
    have hU_open : IsOpen U_balls := isOpen_biUnion fun _ _ => isOpen_ball
    set K_rem : Set ℂ := K_box \ U_balls
    have hK_rem_comp : IsCompact K_rem := hK_box_comp.diff hU_open
    have hK_rem_nz : ∀ z ∈ K_rem, riemannHeat s₀ z ≠ 0 := by
      intro z ⟨hzK, hzU⟩ hz0
      obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩ := hzK
      have hcb : (x : ℂ) + (y : ℂ) * I ∈ closedBall (0 : ℂ) (M₀ + 2) := by
        rw [mem_closedBall, dist_zero_right]
        have hx' : |x| ≤ M₀ := abs_le.mpr hx
        have hy' : |y| ≤ 1 := abs_le.mpr hy
        have hn := Complex.norm_le_abs_re_add_abs_im ((x : ℂ) + (y : ℂ) * I)
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, mul_zero, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
          Complex.mul_im, zero_add] at hn
        linarith
      have hmemE : (x : ℂ) + (y : ℂ) * I ∈ E_all :=
        (Set.Finite.mem_toFinset _).mpr ⟨hcb, hz0⟩
      exact hzU (mem_iUnion₂.mpr ⟨_, hmemE, mem_ball_self (hrpos _)⟩)
    have hev_rem : ∀ᶠ s in 𝓝[>] s₀, ∀ z ∈ K_rem, riemannHeat s z ≠ 0 := by
      rcases K_rem.eq_empty_or_nonempty with hemp | hne
      · exact Eventually.of_forall fun _ z hz => by rw [hemp] at hz; exact False.elim hz
      · obtain ⟨w₀, hw₀, hmin⟩ := hK_rem_comp.exists_isMinOn hne
          (differentiable_riemannHeat hs₀_nn).continuous.norm.continuousOn
        have hμ : 0 < ‖riemannHeat s₀ w₀‖ := norm_pos_iff.mpr (hK_rem_nz w₀ hw₀)
        have hunif := (Metric.tendstoUniformlyOn_iff.mp
          ((tendstoLocallyUniformly_iff_forall_isCompact.mp
            (tendstoLocallyUniformly_riemannHeat_nhdsGT hs₀_nn)) K_rem hK_rem_comp)) _ hμ
        filter_upwards [hunif, self_mem_nhdsWithin] with s hs hsgt z hz h0
        have hs0 : 0 ≤ s := hs₀_nn.trans (Set.mem_Ioi.mp hsgt).le
        have h1 := hs z hz
        rw [max_eq_left hs0, dist_eq_norm, h0, sub_zero] at h1
        exact (not_lt.mpr (hmin hz)) h1
    have hev_in : ∀ᶠ s in 𝓝[>] s₀, ∀ e ∈ E_in,
        zeroSumBall (riemannHeat s) e (r e) = (zeroMult (riemannHeat s₀) e : ℂ) ∧
          ∀ w ∈ sphere e (r e), riemannHeat s w ≠ 0 :=
      (Filter.eventually_all_finset E_in).mpr fun e _ => (hρ₀prop e (r e) (hrpos e) (hr₀ e)).2.2
    have hreal_ev : ∀ e ∈ E_all.filter (fun e => e.im = 0), ∀ᶠ s in 𝓝[>] s₀,
        ∀ w ∈ ball e (r e), riemannHeat s w = 0 → w.im = 0 := by
      intro e he
      have him : e.im = 0 := (Finset.mem_filter.mp he).2
      obtain ⟨δr, hδr, hrp⟩ := hρ₁prop e (r e) (hrpos e) (hr₁ e)
      have he' : ((e.re : ℝ) : ℂ) = e := Complex.ext (by simp) (by simp [him])
      rw [he'] at hrp
      filter_upwards [Ioo_mem_nhdsGT (by linarith : s₀ < s₀ + δr)] with s hs
      exact hrp s hs.1 hs.2
    have hev_real := (Filter.eventually_all_finset _).mpr hreal_ev
    -- Continuity of `R` at `s₀` within `Icc 0 t`
    have hR_at := Metric.continuousWithinAt_iff.mp (hRcont s₀ ⟨hs₀.1, hs₀.2.le⟩) η hη_pos
    obtain ⟨δ_R, hδ_R, hR_ball⟩ := hR_at
    obtain ⟨δ₁, hδ₁, hδ₁_ev⟩ := Metric.mem_nhdsWithin_iff.mp
      ((hev_rem.and hev_in).and hev_real)
    refine ⟨min δ_R δ₁, lt_min hδ_R hδ₁, fun s hsI hlt => ?_⟩
    have hs_pos : 0 < s := lt_of_le_of_lt hs₀_nn hsI.1
    have hs_mem1 : s ∈ ball s₀ δ₁ ∩ Ioi s₀ :=
      ⟨by rw [mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hsI.1)]
          exact (sub_lt_iff_lt_add'.mpr hlt).trans_le (min_le_right _ _), hsI.1⟩
    obtain ⟨⟨hs_rem, hs_in⟩, hs_real⟩ := hδ₁_ev hs_mem1
    have hs_R : |R s - R s₀| < η := by
      have hd_s : dist s s₀ < δ_R := by
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hsI.1)]
        exact (sub_lt_iff_lt_add'.mpr hlt).trans_le (min_le_left _ _)
      simpa [Real.dist_eq] using hR_ball ⟨hs_pos.le, hsI.2⟩ hd_s
    -- Every nonreal zero of `H_s` with `|w.re| < R s` lies in `ball e (r e)` for some `e ∈ E_in`
    have hdiffs := differentiable_riemannHeat hs_pos.le
    have hZe : ∀ e ∈ E_in, ∃ Z : Finset ℂ, (∀ ρ ∈ Z, ρ ∈ ball e (r e)) ∧
        (∀ z ∈ ball e (r e), riemannHeat s z = 0 ↔ z ∈ Z) ∧
        zeroSumBall (riemannHeat s) e (r e) = ∑ ρ ∈ Z, (zeroMult (riemannHeat s) ρ : ℂ) :=
      fun e he => exists_zeroSet_zeroSumBall (hrpos e) (by linarith [hrpos e] : r e < 2 * r e)
        isOpen_univ (subset_univ _) hdiffs.differentiableOn (hs_in e he).2
    choose! W hWb hWz hWs using hZe
    have hWdisj : (E_in : Set ℂ).PairwiseDisjoint W := by
      intro e he e' he' hne
      refine Finset.disjoint_left.mpr fun z hz hz' => ?_
      exact (Set.disjoint_left.mp (hdisj e (Finset.mem_filter.mp he).1 e'
        (Finset.mem_filter.mp he').1 hne)) (hWb e he z hz) (hWb e' he' z hz')
    set F_s := (riemannHeat_nonreal_zeros_finite hs_pos).toFinset.filter (fun w => |w.re| < R s)
    have hF_sub : F_s ⊆ E_in.biUnion W := by
      intro w hw
      obtain ⟨hwF, hwre⟩ := Finset.mem_filter.mp hw
      obtain ⟨hw0, hwim⟩ := (Set.Finite.mem_toFinset _).mp hwF
      have hw_im1 : |w.im| ≤ 1 := (abs_im_le_half_of_riemannHeat_eq_zero hs_pos hw0).trans (by norm_num)
      have hw_reM : |w.re| ≤ M₀ := by
        have h1 := (abs_lt.mp hs_R).2
        have h2 : R s₀ ≤ max (R s₀) 0 := le_max_left _ _
        dsimp only [M₀]; linarith
      have hwK : w ∈ K_box := ⟨(w.re, w.im), ⟨abs_le.mp hw_reM, abs_le.mp hw_im1⟩,
        Complex.re_add_im w⟩
      have hwU : w ∈ U_balls := by
        by_contra hn; exact hs_rem w ⟨hwK, hn⟩ hw0
      obtain ⟨e, heA, hwe⟩ := mem_iUnion₂.mp hwU
      have he_im : e.im ≠ 0 := fun him0 =>
        hwim (hs_real e (Finset.mem_filter.mpr ⟨heA, him0⟩) w hwe hw0)
      have he_in : |e.re| < R s₀ := by
        by_contra hge
        have hne_eq : |e.re| ≠ R s₀ := fun heq =>
          he_im (hbarrier s₀ ⟨hs₀.1, hs₀.2.le⟩ e ((Set.Finite.mem_toFinset _).mp heA).2 heq)
        have hgt : R s₀ < |e.re| := lt_of_le_of_ne (not_lt.mp hge) hne_eq.symm
        have hout := hη_out e (Finset.mem_filter.mpr ⟨heA, he_im, hgt⟩)
        have hdist_re : |(|e.re| - |w.re|)| ≤ ‖w - e‖ :=
          (abs_abs_sub_abs_le_abs_sub e.re w.re).trans
            (by rw [abs_sub_comm, ← Complex.sub_re]; exact Complex.abs_re_le_norm _)
        have hwe_norm : ‖w - e‖ < η := (mem_ball_iff_norm.mp hwe).trans_le (hrη e)
        have hRs := (abs_lt.mp hs_R).2
        linarith [(abs_le.mp hdist_re).2]
      have heI : e ∈ E_in := Finset.mem_filter.mpr ⟨heA, he_im, he_in⟩
      exact Finset.mem_biUnion.mpr ⟨e, heI, (hWz e heI w hwe).mp hw0⟩
    have hsum_in : ∑ e ∈ E_in, zeroMult (riemannHeat s₀) e =
        riemannHeatWindowNonrealCount s₀ (R s₀) := by
      rcases eq_or_lt_of_le hs₀_nn with rfl | hs₀_pos
      · rw [riemannHeatWindowNonrealCount_zero]
        unfold xiWindowNonrealZeroCount
        congr 1; ext e
        simp only [E_in, E_all, Finset.mem_filter, Set.Finite.mem_toFinset, mem_closedBall,
          dist_zero_right, mem_setOf_eq]
        refine ⟨fun ⟨⟨_, h0⟩, him, hre⟩ => ⟨h0, him, hre⟩, fun ⟨h0, him, hre⟩ => ⟨⟨?_, h0⟩, him, hre⟩⟩
        have him2 := (abs_im_lt_half_of_riemannHeat_zero h0).le
        have hn := Complex.norm_le_abs_re_add_abs_im e
        have h2 : R 0 ≤ max (R 0) 0 := le_max_left _ _
        dsimp only [M₀]; linarith
      · rw [riemannHeatWindowNonrealCount_pos hs₀_pos]
        congr 1; ext e
        simp only [E_in, E_all, Finset.mem_filter, Set.Finite.mem_toFinset, mem_closedBall,
          dist_zero_right, mem_setOf_eq]
        refine ⟨fun ⟨⟨_, h0⟩, him, hre⟩ => ⟨⟨h0, him⟩, hre⟩, fun ⟨⟨h0, him⟩, hre⟩ => ⟨⟨?_, h0⟩, him, hre⟩⟩
        have him2 := abs_im_le_half_of_riemannHeat_eq_zero hs₀_pos h0
        have hn := Complex.norm_le_abs_re_add_abs_im e
        have h2 : R s₀ ≤ max (R s₀) 0 := le_max_left _ _
        dsimp only [M₀]; linarith
    rw [riemannHeatWindowNonrealCount_pos hs_pos, ← hsum_in]
    calc ∑ z ∈ F_s, zeroMult (riemannHeat s) z
        ≤ ∑ z ∈ E_in.biUnion W, zeroMult (riemannHeat s) z := Finset.sum_le_sum_of_subset hF_sub
      _ = ∑ e ∈ E_in, ∑ z ∈ W e, zeroMult (riemannHeat s) z := Finset.sum_biUnion hWdisj
      _ = ∑ e ∈ E_in, zeroMult (riemannHeat s₀) e := by
          refine Finset.sum_congr rfl fun e he => ?_
          have h := (hWs e he).symm.trans (hs_in e he).1
          exact_mod_cast h
  · -- Left-local lower semicontinuity on `(0, t]`
    have hs₁_pos : 0 < s₁ := hs₁.1
    set Enr := (riemannHeat_nonreal_zeros_finite hs₁_pos).toFinset.filter (fun e => |e.re| < R s₁)
    rcases Enr.eq_empty_or_nonempty with hemp | hne
    · refine ⟨1, one_pos, fun s _ _ => ?_⟩
      rw [riemannHeatWindowNonrealCount_pos hs₁_pos]
      change ∑ z ∈ Enr, zeroMult (riemannHeat s₁) z ≤ _
      rw [hemp, Finset.sum_empty]
      exact Nat.zero_le _
    · set η := Enr.inf' hne (fun e => R s₁ - |e.re|)
      have hη_pos : 0 < η := (Finset.lt_inf'_iff hne).mpr fun e he =>
        sub_pos.mpr (Finset.mem_filter.mp he).2
      choose ρ₀ hρ₀ hρ₀prop using fun e => eventually_zeroSumBall_riemannHeat_eq hs₁_pos e
      obtain ⟨d, hd, hdsep⟩ := exists_pos_sep Enr
      set r : ℂ → ℝ := fun e => min (min (ρ₀ e) (|e.im| / 2)) (min (d / 3) (η / 3))
      have hrpos : ∀ e ∈ Enr, 0 < r e := fun e he => by
        have him : e.im ≠ 0 := ((Set.Finite.mem_toFinset _).mp (Finset.mem_filter.mp he).1).2
        exact lt_min (lt_min (hρ₀ e) (div_pos (abs_pos.mpr him) two_pos))
          (lt_min (by positivity) (by positivity))
      have havoid : ∀ e ∈ Enr, ∀ w ∈ ball e (r e), w.im ≠ 0 := by
        intro e he w hw hw0
        have him : e.im ≠ 0 := ((Set.Finite.mem_toFinset _).mp (Finset.mem_filter.mp he).1).2
        have h1 : |(w - e).im| ≤ ‖w - e‖ := Complex.abs_im_le_norm _
        rw [Complex.sub_im, hw0, zero_sub, abs_neg] at h1
        have hr2 : r e ≤ |e.im| / 2 := (min_le_left _ _).trans (min_le_right _ _)
        linarith [mem_ball_iff_norm.mp hw, abs_pos.mpr him]
      have hdisj : ∀ e ∈ Enr, ∀ e' ∈ Enr, e ≠ e' → Disjoint (ball e (r e)) (ball e' (r e')) := by
        intro e he e' he' hne
        refine Set.disjoint_left.mpr fun w hw hw' => ?_
        have h1 := hdsep e he e' he' hne
        have h2 := dist_triangle e w e'
        rw [mem_ball] at hw hw'; rw [dist_comm] at hw
        have h3 : r e ≤ d / 3 := (min_le_right _ _).trans (min_le_left _ _)
        have h4 : r e' ≤ d / 3 := (min_le_right _ _).trans (min_le_left _ _)
        linarith
      have hev_balls : ∀ᶠ s in 𝓝 s₁, ∀ e ∈ Enr,
          zeroSumBall (riemannHeat s) e (r e) = (zeroMult (riemannHeat s₁) e : ℂ) ∧
            ∀ w ∈ sphere e (r e), riemannHeat s w ≠ 0 :=
        (Filter.eventually_all_finset Enr).mpr fun e he =>
          (hρ₀prop e (r e) (hrpos e he) ((min_le_left _ _).trans (min_le_left _ _))).2.2
      obtain ⟨δ₁, hδ₁, hδ₁_ev⟩ := Metric.eventually_nhds_iff.mp hev_balls
      obtain ⟨δ_R, hδ_R, hR_ball⟩ := Metric.continuousWithinAt_iff.mp
        (hRcont s₁ ⟨hs₁_pos.le, hs₁.2⟩) (η / 3) (by positivity)
      refine ⟨min (s₁ / 2) (min δ₁ δ_R), lt_min (by positivity) (lt_min hδ₁ hδ_R),
        fun s hsI hgt => ?_⟩
      have hs_pos : 0 < s := by
        have : min (s₁ / 2) (min δ₁ δ_R) ≤ s₁ / 2 := min_le_left _ _
        linarith
      have hdist : dist s s₁ < min δ₁ δ_R := by
        rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hsI.2)]
        have : min (s₁ / 2) (min δ₁ δ_R) ≤ min δ₁ δ_R := min_le_right _ _
        linarith
      have hs_b := hδ₁_ev (hdist.trans_le (min_le_left _ _))
      have hs_R : |R s - R s₁| < η / 3 := by
        simpa [Real.dist_eq] using hR_ball ⟨hs_pos.le, hsI.2.le.trans hs₁.2⟩
          (hdist.trans_le (min_le_right _ _))
      have hdiffs := differentiable_riemannHeat hs_pos.le
      have hZe : ∀ e ∈ Enr, ∃ Z : Finset ℂ, (∀ ρ ∈ Z, ρ ∈ ball e (r e)) ∧
          (∀ z ∈ ball e (r e), riemannHeat s z = 0 ↔ z ∈ Z) ∧
          zeroSumBall (riemannHeat s) e (r e) = ∑ ρ ∈ Z, (zeroMult (riemannHeat s) ρ : ℂ) :=
        fun e he => exists_zeroSet_zeroSumBall (hrpos e he) (by linarith [hrpos e he] : r e < 2 * r e)
          isOpen_univ (subset_univ _) hdiffs.differentiableOn (hs_b e he).2
      choose! W hWb hWz hWs using hZe
      have hWdisj : (Enr : Set ℂ).PairwiseDisjoint W := by
        intro e he e' he' hne
        refine Finset.disjoint_left.mpr fun z hz hz' => ?_
        exact (Set.disjoint_left.mp (hdisj e he e' he' hne)) (hWb e he z hz) (hWb e' he' z hz')
      set F_s := (riemannHeat_nonreal_zeros_finite hs_pos).toFinset.filter (fun w => |w.re| < R s)
      have hW_sub : Enr.biUnion W ⊆ F_s := by
        intro w hw
        obtain ⟨e, he, hwe⟩ := Finset.mem_biUnion.mp hw
        have hwb := hWb e he w hwe
        have hw0 := (hWz e he w hwb).mpr hwe
        have hwim := havoid e he w hwb
        have he_gap : η ≤ R s₁ - |e.re| := Finset.inf'_le _ he
        have hr_eta : r e ≤ η / 3 := (min_le_right _ _).trans (min_le_right _ _)
        have hre_diff : |w.re| - |e.re| ≤ ‖w - e‖ :=
          (abs_sub_abs_le_abs_sub w.re e.re).trans
            (by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _)
        have hwnorm : ‖w - e‖ < η / 3 := (mem_ball_iff_norm.mp hwb).trans_le hr_eta
        have hRs1 := (abs_lt.mp hs_R).1
        refine Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr ⟨hw0, hwim⟩, ?_⟩
        linarith
      rw [riemannHeatWindowNonrealCount_pos hs₁_pos, riemannHeatWindowNonrealCount_pos hs_pos]
      calc ∑ e ∈ Enr, zeroMult (riemannHeat s₁) e
          = ∑ e ∈ Enr, ∑ z ∈ W e, zeroMult (riemannHeat s) z := by
            refine Finset.sum_congr rfl fun e he => ?_
            have h := (hs_b e he).1.symm.trans (hWs e he)
            exact_mod_cast h
        _ = ∑ z ∈ Enr.biUnion W, zeroMult (riemannHeat s) z := (Finset.sum_biUnion hWdisj).symm
        _ ≤ ∑ z ∈ F_s, zeroMult (riemannHeat s) z := Finset.sum_le_sum_of_subset hW_sub

/-- Normalized upper-half-plane corollary of moving-barrier descent: `N_↑(t) ≤ O(R 0)`. -/
theorem upperHalfNonrealZeroCount_le_collisionCharge_of_barrier {t : ℝ} (ht : 0 < t)
    (ht8 : t ≤ 1 / 8) {R : ℝ → ℝ} (hRcont : ContinuousOn R (Icc 0 t))
    (hRkkl : 2 * Real.pi * Real.exp (40 / t) ≤ R t)
    (hbarrier : ∀ s ∈ Icc 0 t, ∀ z : ℂ, riemannHeat s z = 0 → |z.re| = R s → z.im = 0) :
    upperHalfNonrealZeroCount t ≤ xiHorizontalCollisionCharge (R 0) := by
  have h := (nonrealZeroCount_le_two_mul_collisionCharge_of_barrier ht ht8 hRcont hRkkl hbarrier).2
  rw [nonrealZeroCount_eq_two_mul_upperHalfNonrealZeroCount] at h
  omega

/-! ## §4. Unconditional global heat-by-charge bound and finiteness equivalence -/

/-- **Global charge-to-heat inequality.** If `O(T) ≤ M` for all `T ≥ 0`, then `N(t) ≤ 2M` for every
`t > 0`. -/
theorem nonrealZeroCount_le_two_mul_of_collisionCharge_bdd {M : ℕ}
    (hM : ∀ T : ℝ, 0 ≤ T → xiHorizontalCollisionCharge T ≤ M) {t : ℝ} (ht : 0 < t) :
    nonrealZeroCount t ≤ 2 * M := by
  classical
  have hZ : {z : ℂ | riemannHeat 0 z = 0 ∧ z.im ≠ 0}.Finite := by
    by_contra hinf
    obtain ⟨E, hEsub, hEcard⟩ := Set.Infinite.exists_subset_card_eq hinf (2 * M + 1)
    set T_E : ℝ := ∑ z ∈ E, (|z.re| + 1)
    have hTE_nn : 0 ≤ T_E := Finset.sum_nonneg fun _ _ => by positivity
    have hsub : E ⊆ (riemannHeat_zero_window_zeros_finite T_E).toFinset := by
      intro z hz
      obtain ⟨hz0, hzim⟩ := hEsub hz
      have hle := Finset.single_le_sum (f := fun w : ℂ => |w.re| + 1) (fun _ _ => by positivity) hz
      exact (Set.Finite.mem_toFinset _).mpr ⟨hz0, hzim, by dsimp only [T_E]; linarith⟩
    have h1 : 2 * M + 1 ≤ xiWindowNonrealZeroCount T_E := by
      calc 2 * M + 1 = ∑ _z ∈ E, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one, hEcard]
        _ ≤ ∑ z ∈ E, zeroMult (riemannHeat 0) z :=
            Finset.sum_le_sum fun z hz => one_le_zeroMult_riemannHeat le_rfl (hEsub hz).1
        _ ≤ xiWindowNonrealZeroCount T_E := Finset.sum_le_sum_of_subset hsub
    have h2 := (xiWindowNonrealZeroCount_le_two_mul_collisionCharge T_E).trans
      (Nat.mul_le_mul_left 2 (hM T_E hTE_nn))
    omega
  have hfin := finite_nonrealCopies_of_finite_zeros hZ
  set E := hfin.toFinset.image xiSpectralPoint
  set T_K : ℝ := ∑ e ∈ E, (|e.re| + 1)
  have hTK_nn : 0 ≤ T_K := Finset.sum_nonneg fun _ _ => by positivity
  have hE_sub : E ⊆ (riemannHeat_zero_window_zeros_finite T_K).toFinset := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
    have hle := Finset.single_le_sum (f := fun w : ℂ => |w.re| + 1) (fun _ _ => by positivity) he
    refine (Set.Finite.mem_toFinset _).mpr ⟨?_, (Set.Finite.mem_toFinset hfin).mp hq, by
      dsimp only [T_K]; linarith⟩
    rw [DeBruijn.riemannHeat_zero_eq_XiC]
    exact XiC_xiSpectralPoint_eq_zero q
  have hcard_le : hfin.toFinset.card ≤ 2 * M := by
    rw [card_nonrealCopies_eq_sum_zeroMult hfin]
    exact (Finset.sum_le_sum_of_subset hE_sub).trans
      ((xiWindowNonrealZeroCount_le_two_mul_collisionCharge T_K).trans
        (Nat.mul_le_mul_left 2 (hM T_K hTK_nn)))
  exact (nonrealZeroCount_le_of_finite_nonreal_zeros hfin ht).trans hcard_le

/-- Normalized upper-half-plane global bound: `(∀ T ≥ 0, O(T) ≤ M) → N_↑(t) ≤ M`. -/
theorem upperHalfNonrealZeroCount_le_of_collisionCharge_bdd {M : ℕ}
    (hM : ∀ T : ℝ, 0 ≤ T → xiHorizontalCollisionCharge T ≤ M) {t : ℝ} (ht : 0 < t) :
    upperHalfNonrealZeroCount t ≤ M := by
  have h := nonrealZeroCount_le_two_mul_of_collisionCharge_bdd hM ht
  rw [nonrealZeroCount_eq_two_mul_upperHalfNonrealZeroCount] at h
  omega

/-- **Uniform heat-count boundedness ↔ uniform collision-charge boundedness.** -/
theorem exists_nonrealZeroCount_le_iff_exists_collisionCharge_le :
    (∃ B : ℕ, ∀ t, 0 < t → nonrealZeroCount t ≤ B) ↔
      (∃ M : ℕ, ∀ T, 0 ≤ T → xiHorizontalCollisionCharge T ≤ M) := by
  classical
  constructor
  · intro hB
    have hZ := finite_nonreal_zeros_iff_exists_nonrealZeroCount_le.mpr hB
    set Z := hZ.toFinset
    set T_max : ℝ := ∑ z ∈ Z, (|z.re| + 1)
    have hTm_nn : 0 ≤ T_max := Finset.sum_nonneg fun _ _ => by positivity
    refine ⟨xiHorizontalCollisionCharge T_max, fun T hT => ?_⟩
    rcases le_or_gt T T_max with hle | hgt
    · exact xiHorizontalCollisionCharge_mono hle
    · -- Above `T_max`, `ξ` has no off-line zeros, so every horizontal fibre is a singleton on `Re = 1/2`
      have hno_off : ∀ ρ : ℂ, xi ρ = 0 → T_max ≤ ρ.im → ρ.re = 1 / 2 := by
        intro ρ hxi hge
        by_contra hne
        have hz_mem : (ρ - 1 / 2) * (-I) ∈ Z := by
          refine (Set.Finite.mem_toFinset hZ).mpr ⟨?_, ?_⟩
          · rw [riemannHeat_zero, show (1 / 2 : ℂ) + I * ((ρ - 1 / 2) * (-I)) = ρ by
              ring_nf; rw [I_sq]; ring]
            exact hxi
          · simp; intro h; apply hne; linarith
        have hle := Finset.single_le_sum (f := fun w : ℂ => |w.re| + 1) (fun _ _ => by positivity) hz_mem
        have hre : ((ρ - 1 / 2) * (-I)).re = ρ.im := by simp
        rw [hre] at hle
        dsimp only [T_max] at hge
        linarith [le_abs_self ρ.im]
      unfold xiHorizontalCollisionCharge
      set S := (stripZeros_finite T).toFinset
      rw [← Finset.sum_filter_add_sum_filter_not S (fun ρ => T_max ≤ ρ.im)]
      have hhigh : ∑ ρ ∈ S.filter (fun ρ => T_max ≤ ρ.im),
          (analyticOrderAt xi ρ).toNat *
            (xiHorizontalMultiplicity ρ.im - (analyticOrderAt xi ρ).toNat) = 0 := by
        refine Finset.sum_eq_zero fun ρ hρ => ?_
        obtain ⟨hρS, hge⟩ := Finset.mem_filter.mp hρ
        have hρxi := ((Set.Finite.mem_toFinset _).mp hρS).2
        have hρre := hno_off ρ hρxi hge
        rw [horizontalMultiplicity_sub_order_eq_sum_same_im_erase hρS]
        suffices ((S.filter (fun z => z.im = ρ.im)).erase ρ) = ∅ by rw [this]; simp
        refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
        obtain ⟨hzne, hzF⟩ := Finset.mem_erase.mp hz
        obtain ⟨hzS, hzim⟩ := Finset.mem_filter.mp hzF
        have hzre := hno_off z ((Set.Finite.mem_toFinset _).mp hzS).2 (by rw [hzim]; exact hge)
        exact hzne (Complex.ext (hzre.trans hρre.symm) hzim)
      have hlow : S.filter (fun ρ => ¬ T_max ≤ ρ.im) = (stripZeros_finite T_max).toFinset := by
        ext ρ
        simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset, not_le]
        exact ⟨fun ⟨⟨⟨h1, h2, h3, _⟩, hz⟩, hlt⟩ => ⟨⟨h1, h2, h3, hlt⟩, hz⟩,
          fun ⟨⟨h1, h2, h3, h4⟩, hz⟩ => ⟨⟨⟨h1, h2, h3, h4.trans hgt⟩, hz⟩, h4⟩⟩
      rw [hhigh, zero_add, hlow]
  · rintro ⟨M, hM⟩
    exact ⟨2 * M, fun t ht => nonrealZeroCount_le_two_mul_of_collisionCharge_bdd hM ht⟩

/-! ## §5. Reverse dyadic finite-height heat-to-charge bound -/

/-- Shallow off-line multiplicity (`0 < |Re ρ − 1/2| < d`) in the ordinate window `[A, B)`. -/
def xiWindowShallowOffLineOrder (A B d : ℝ) : ℕ :=
  ∑ ρ ∈ (stripZeros_finite B).toFinset.filter
    (fun ρ => A ≤ ρ.im ∧ ρ.re ≠ 1 / 2 ∧ |ρ.re - 1 / 2| < d),
    (analyticOrderAt xi ρ).toNat

/-- General interval bound for `O(B) − O(A)` (`A ≤ B`) in terms of a bound `K` on local unit-window
multiplicities across `[A, B)` and the off-line multiplicity in `[A, B)`. -/
theorem xiHorizontalCollisionCharge_sub_le_two_mul_offLine {A B : ℝ} (hAB : A ≤ B) {K : ℕ}
    (hK : ∀ ρ ∈ (stripZeros_finite B).toFinset, A ≤ ρ.im → xiUnitWindowOrder ρ.im ≤ K) :
    xiHorizontalCollisionCharge B - xiHorizontalCollisionCharge A ≤
      2 * K * ∑ ρ ∈ (stripZeros_finite B).toFinset.filter (fun ρ => A ≤ ρ.im ∧ ρ.re ≠ 1 / 2),
        (analyticOrderAt xi ρ).toNat := by
  classical
  set SB := (stripZeros_finite B).toFinset
  set W := SB.filter (fun ρ => A ≤ ρ.im)
  have hlow : SB.filter (fun ρ => ¬ A ≤ ρ.im) = (stripZeros_finite A).toFinset := by
    ext ρ
    simp only [SB, Finset.mem_filter, Set.Finite.mem_toFinset, not_le]
    exact ⟨fun ⟨⟨⟨h1, h2, h3, _⟩, hz⟩, hlt⟩ => ⟨⟨h1, h2, h3, hlt⟩, hz⟩,
      fun ⟨⟨h1, h2, h3, h4⟩, hz⟩ => ⟨⟨⟨h1, h2, h3, h4.trans_le hAB⟩, hz⟩, h4⟩⟩
  have hOB : xiHorizontalCollisionCharge B =
      xiHorizontalCollisionCharge A + ∑ ρ ∈ W, xiCollisionTerm ρ := by
    unfold xiHorizontalCollisionCharge xiCollisionTerm
    have := (Finset.sum_filter_add_sum_filter_not SB (fun ρ => A ≤ ρ.im)
      (fun ρ => (analyticOrderAt xi ρ).toNat *
        (xiHorizontalMultiplicity ρ.im - (analyticOrderAt xi ρ).toNat))).symm
    rw [this, hlow, add_comm]
  have hsub : xiHorizontalCollisionCharge B - xiHorizontalCollisionCharge A =
      ∑ ρ ∈ W, xiCollisionTerm ρ := by omega
  rw [hsub]
  -- Bound `xiHorizontalMultiplicity ρ.im ≤ xiUnitWindowOrder ρ.im ≤ K` for every `ρ ∈ W`
  have hH_le : ∀ ρ ∈ W, xiHorizontalMultiplicity ρ.im ≤ K := by
    intro ρ hρ
    obtain ⟨hρB, hAρ⟩ := Finset.mem_filter.mp hρ
    have hsub_u : stripHeightFinset ρ.im ⊆ xiUnitWindowZeros ρ.im := by
      intro z hz
      obtain ⟨h0, h1, hzim, hxi⟩ := mem_stripHeightFinset.mp hz
      have him0 : 0 ≤ z.im := hzim.trans_ge ((Set.Finite.mem_toFinset _).mp hρB).1.2.2.1
      refine mem_xiUnitWindowZeros.mpr ⟨(Set.Finite.mem_toFinset _).mpr
        ⟨⟨h0, h1, him0, by linarith⟩, hxi⟩, hzim.symm.le⟩
    exact (Finset.sum_le_sum_of_subset hsub_u).trans (hK ρ hρB hAρ)
  set Woff := W.filter (fun ρ => ρ.re ≠ 1 / 2)
  set Wcrit := W.filter (fun ρ => ρ.re = 1 / 2)
  have hsplit := (Finset.sum_filter_add_sum_filter_not W (fun ρ => ρ.re = 1 / 2)
    xiCollisionTerm).symm
  have hoff_le : ∑ ρ ∈ Woff, xiCollisionTerm ρ ≤
      K * ∑ ρ ∈ Woff, (analyticOrderAt xi ρ).toNat := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    unfold xiCollisionTerm
    rw [mul_comm K]
    exact Nat.mul_le_mul_left _ ((Nat.sub_le _ _).trans (hH_le ρ (Finset.mem_filter.mp hρ).1))
  have hcrit_le : ∑ ρ ∈ Wcrit, xiCollisionTerm ρ ≤
      K * ∑ ρ ∈ Woff, (analyticOrderAt xi ρ).toNat := by
    have hterm : ∀ ρ ∈ Wcrit, xiCollisionTerm ρ =
        ∑ z ∈ Woff.filter (fun z => z.im = ρ.im),
          (analyticOrderAt xi ρ).toNat * (analyticOrderAt xi z).toNat := by
      intro ρ hρ
      obtain ⟨hρW, hρre⟩ := Finset.mem_filter.mp hρ
      obtain ⟨hρB, hAρ⟩ := Finset.mem_filter.mp hρW
      unfold xiCollisionTerm
      rw [horizontalMultiplicity_sub_order_eq_sum_same_im_erase hρB, Finset.mul_sum]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext z
      simp only [Finset.mem_erase, Finset.mem_filter, Woff, W]
      refine ⟨fun ⟨hzne, hzB, hzim⟩ => ⟨⟨⟨hzB, by rw [hzim]; exact hAρ⟩, fun hzre =>
        hzne (Complex.ext (hzre.trans hρre.symm) hzim)⟩, hzim⟩,
        fun ⟨⟨⟨hzB, _⟩, hzre⟩, hzim⟩ => ⟨fun h => hzre (h ▸ hρre), hzB, hzim⟩⟩
    calc ∑ ρ ∈ Wcrit, xiCollisionTerm ρ
        = ∑ ρ ∈ Wcrit, ∑ z ∈ Woff.filter (fun z => z.im = ρ.im),
            (analyticOrderAt xi ρ).toNat * (analyticOrderAt xi z).toNat :=
          Finset.sum_congr rfl hterm
      _ = ∑ z ∈ Woff, ∑ ρ ∈ Wcrit.filter (fun ρ => z.im = ρ.im),
            (analyticOrderAt xi ρ).toNat * (analyticOrderAt xi z).toNat := by
          simp_rw [Finset.sum_filter]; rw [Finset.sum_comm]
      _ ≤ ∑ z ∈ Woff, K * (analyticOrderAt xi z).toNat := by
          refine Finset.sum_le_sum fun z hz => ?_
          rw [← Finset.sum_mul]
          refine Nat.mul_le_mul_right _ ?_
          have hsub_fib : Wcrit.filter (fun ρ => z.im = ρ.im) ⊆ stripHeightFinset z.im := by
            intro ρ hρ
            obtain ⟨hρc, hzim⟩ := Finset.mem_filter.mp hρ
            obtain ⟨⟨h0, h1, _, _⟩, hxi⟩ := (Set.Finite.mem_toFinset _).mp
              (Finset.mem_filter.mp (Finset.mem_filter.mp hρc).1).1
            exact mem_stripHeightFinset.mpr ⟨h0, h1, hzim.symm, hxi⟩
          exact (Finset.sum_le_sum_of_subset hsub_fib).trans
            (hH_le z (Finset.mem_filter.mp hz).1)
      _ = K * ∑ z ∈ Woff, (analyticOrderAt xi z).toNat := (Finset.mul_sum _ _ _).symm
  have hWoff_eq : Woff = SB.filter (fun ρ => A ≤ ρ.im ∧ ρ.re ≠ 1 / 2) := by
    ext ρ; simp [Woff, W, and_assoc]
  change ∑ ρ ∈ W, xiCollisionTerm ρ =
    (∑ ρ ∈ Wcrit, xiCollisionTerm ρ) + (∑ ρ ∈ Woff, xiCollisionTerm ρ) at hsplit
  rw [hsplit, ← hWoff_eq, two_mul, add_mul]
  exact add_le_add hcrit_le hoff_le

/-- **Reverse dyadic finite-height heat-to-charge bound.** There exist absolute constants
`c > 0`, `C₁ > 0`, `C₂ > 0`, and `X₀ ≥ 4096` such that for every `X ≥ X₀`, depth threshold
`0 < d ≤ 1/2`, and heat time `0 < t` with `t * log X ≤ c * d²`:
`O(2X) − O(X) ≤ C₁ (log X)² N(t) + C₂ (log X) n_{off, < d}([X, 2X))`. -/
theorem exists_dyadicCollisionCharge_le_log_sq_mul_nonrealZeroCount_add_shallow :
    ∃ c C₁ C₂ X₀ : ℝ, 0 < c ∧ 0 < C₁ ∧ 0 < C₂ ∧ 4096 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ d : ℝ, 0 < d → d ≤ 1 / 2 →
        ∀ t : ℝ, 0 < t → t * Real.log X ≤ c * d ^ 2 →
          ((xiHorizontalCollisionCharge (2 * X) - xiHorizontalCollisionCharge X : ℕ) : ℝ) ≤
            C₁ * Real.log X ^ 2 * nonrealZeroCount t +
              C₂ * Real.log X * xiWindowShallowOffLineOrder X (2 * X) d := by
  classical
  obtain ⟨c, C_d, hc, hCd, X₁, hX₁, hdeep_thm⟩ :=
    exists_card_deep_le_heat_count_at_uniform_depth_scale
  obtain ⟨C_loc, hCloc, hev_loc⟩ := exists_xiUnitWindowOrder_le_log
  obtain ⟨T_loc, hT_loc⟩ := eventually_atTop.mp hev_loc
  set K_const : ℝ := 2 * C_loc + 1
  have hKc_pos : 0 < K_const := by positivity
  refine ⟨c, 2 * K_const * C_d, 2 * K_const, max X₁ (max T_loc 4096),
    hc, by positivity, by positivity, le_trans (le_max_right _ _) (le_max_right _ _),
    fun X hX₀ d hd hd2 t ht htX => ?_⟩
  have hXX₁ : X₁ ≤ X := (le_max_left _ _).trans hX₀
  have hXT : T_loc ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX₀
  have hX4 : 4096 ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX₀
  have hlogX_ge1 : 1 ≤ Real.log X := by
    have : Real.exp 1 ≤ X := Real.exp_one_lt_d9.le.trans (by linarith)
    simpa using Real.log_le_log (Real.exp_pos 1) this
  set K : ℕ := ⌊2 * C_loc * Real.log X⌋₊
  have hK_bound : ∀ ρ ∈ (stripZeros_finite (2 * X)).toFinset, X ≤ ρ.im →
      xiUnitWindowOrder ρ.im ≤ K := by
    intro ρ hρ hXρ
    have hlt2X : ρ.im < 2 * X := ((Set.Finite.mem_toFinset _).mp hρ).1.2.2.2
    have h1 := hT_loc ρ.im (hXT.trans hXρ)
    have hlog2 : Real.log ρ.im ≤ 2 * Real.log X := by
      have : ρ.im ≤ X ^ 2 := by nlinarith
      calc Real.log ρ.im ≤ Real.log (X ^ 2) := Real.log_le_log (by linarith) this
        _ = 2 * Real.log X := by rw [Real.log_pow]; push_cast; rfl
    exact Nat.le_floor (h1.trans (by nlinarith [hCloc]))
  have hcharge_nat := xiHorizontalCollisionCharge_sub_le_two_mul_offLine
    (by linarith : X ≤ 2 * X) hK_bound
  -- Split off-line zeros in `[X, 2X)` into deep (`d ≤ |ρ.re - 1/2|`) and shallow (`|ρ.re - 1/2| < d`)
  set Woff := (stripZeros_finite (2 * X)).toFinset.filter (fun ρ => X ≤ ρ.im ∧ ρ.re ≠ 1 / 2)
  set Wdeep := Woff.filter (fun ρ => d ≤ |ρ.re - 1 / 2|)
  set Wshal := Woff.filter (fun ρ => ¬ d ≤ |ρ.re - 1 / 2|)
  have hsplit_off : ∑ ρ ∈ Woff, (analyticOrderAt xi ρ).toNat =
      ∑ ρ ∈ Wdeep, (analyticOrderAt xi ρ).toNat + ∑ ρ ∈ Wshal, (analyticOrderAt xi ρ).toNat :=
    (Finset.sum_filter_add_sum_filter_not Woff (fun ρ => d ≤ |ρ.re - 1 / 2|) _).symm
  have hshal_eq : ∑ ρ ∈ Wshal, (analyticOrderAt xi ρ).toNat =
      xiWindowShallowOffLineOrder X (2 * X) d := by
    unfold xiWindowShallowOffLineOrder
    congr 1; ext ρ
    simp only [Wshal, Woff, Finset.mem_filter, not_le, and_assoc]
  -- Realize `∑ ρ ∈ Wdeep, m_ρ` as the cardinality of a disjoint union of `XiZeroCopy` fibres
  have hxi_deep : ∀ ρ ∈ Wdeep, xi ρ = 0 := fun ρ hρ =>
    ((Set.Finite.mem_toFinset _).mp (Finset.mem_filter.mp (Finset.mem_filter.mp hρ).1).1).2
  let fib : {ρ // ρ ∈ Wdeep} → Finset XiZeroCopy := fun ρ =>
    xiZeroCopyFiber ⟨ρ.1, mem_xi_divisor_support_of_eq_zero (hxi_deep ρ.1 ρ.2)⟩
  have hdisj : (Wdeep.attach : Set {ρ // ρ ∈ Wdeep}).PairwiseDisjoint fib := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro q hqa hqb
    apply hab; apply Subtype.ext
    have h := (mem_xiZeroCopyFiber.mp hqa).symm.trans (mem_xiZeroCopyFiber.mp hqb)
    exact congrArg (fun r : XiDivisorSupport => (r : ℂ)) h
  set F_deep : Finset XiZeroCopy := Wdeep.attach.biUnion fib
  have hcard_deep : F_deep.card = ∑ ρ ∈ Wdeep, (analyticOrderAt xi ρ).toNat := by
    rw [Finset.card_biUnion hdisj, ← Finset.sum_attach Wdeep]
    exact Finset.sum_congr rfl fun ρ _ => card_xiZeroCopyFiber_eq_order_toNat _
  have hF_prop : ∀ q ∈ F_deep, X ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * X ∧
      d ≤ |(q.1 : ℂ).re - 1 / 2| := by
    intro q hq
    obtain ⟨ρ, _, hqρ⟩ := Finset.mem_biUnion.mp hq
    have hq1 : (q.1 : ℂ) = ρ.1 := by rw [mem_xiZeroCopyFiber.mp hqρ]
    obtain ⟨hρW, hdρ⟩ := Finset.mem_filter.mp ρ.2
    obtain ⟨hρS, hXρ, _⟩ := Finset.mem_filter.mp hρW
    have hlt2X : ρ.1.im < 2 * X := ((Set.Finite.mem_toFinset _).mp hρS).1.2.2.2
    rw [hq1]
    exact ⟨hXρ, hlt2X.le, hdρ⟩
  have hdeep_le := hdeep_thm X hXX₁ d hd hd2 t ht htX F_deep hF_prop
  rw [hcard_deep] at hdeep_le
  push_cast at hdeep_le
  have hK_real : (K : ℝ) ≤ K_const * Real.log X := by
    have h1 : (K : ℝ) ≤ 2 * C_loc * Real.log X := Nat.floor_le (by positivity)
    dsimp only [K_const]; nlinarith [hlogX_ge1]
  have h1 : ((xiHorizontalCollisionCharge (2 * X) - xiHorizontalCollisionCharge X : ℕ) : ℝ) ≤
      2 * (K : ℝ) * ((∑ ρ ∈ Wdeep, (analyticOrderAt xi ρ).toNat : ℝ) +
        xiWindowShallowOffLineOrder X (2 * X) d) := by
    rw [hsplit_off, hshal_eq] at hcharge_nat
    exact_mod_cast hcharge_nat
  have hsum_nn : 0 ≤ (∑ ρ ∈ Wdeep, (analyticOrderAt xi ρ).toNat : ℝ) +
      xiWindowShallowOffLineOrder X (2 * X) d := by positivity
  calc ((xiHorizontalCollisionCharge (2 * X) - xiHorizontalCollisionCharge X : ℕ) : ℝ)
      ≤ 2 * (K : ℝ) * ((∑ ρ ∈ Wdeep, (analyticOrderAt xi ρ).toNat : ℝ) +
          xiWindowShallowOffLineOrder X (2 * X) d) := h1
    _ ≤ 2 * (K_const * Real.log X) *
          (C_d * Real.log X * nonrealZeroCount t + xiWindowShallowOffLineOrder X (2 * X) d) := by
        refine mul_le_mul (by linarith) (by linarith) hsum_nn (by positivity)
    _ = 2 * K_const * C_d * Real.log X ^ 2 * nonrealZeroCount t +
          2 * K_const * Real.log X * xiWindowShallowOffLineOrder X (2 * X) d := by ring

end GaloisForLFunctions.ConjugateDiagonalGeometry

end

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.nonrealZeroCount_eq_two_mul_upperHalfNonrealZeroCount
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.xiWindowNonrealZeroCount_eq_two_mul_offLineOrder
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.eventually_nonrealZeroCount_le_collisionCharge_iff_rh_of_minimal_fibres
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_polyHeat_nonreal_root_inward_drift
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_ball_real_zeros_forward_nonneg
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.nonrealZeroCount_le_two_mul_collisionCharge_of_barrier
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.nonrealZeroCount_le_two_mul_of_collisionCharge_bdd
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_nonrealZeroCount_le_iff_exists_collisionCharge_le
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_dyadicCollisionCharge_le_log_sq_mul_nonrealZeroCount_add_shallow
