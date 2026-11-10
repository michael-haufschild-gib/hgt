import GaloisForLFunctions.InfiniteRankPurityTheory.ADefectOfDegreeKappaHasAtMostKappaExceptionalPoints

/-!
# Sizes on a circle certify the defect inside

A splitting `F = E − E'` has a **defect** in a disc: the zeros of `E` there. The size comparison
`‖E'‖ ≤ ‖E‖` on the boundary circle alone bounds the zeros of `F` in the disc by the defect:

**Theorem** (`encard_zeros_le_of_norm_le_on_sphere`). Let `E = Π_{w ∈ W} (z − w) · E₁` with `W` a
multiset of `κ` points of the open disc and `E₁` without zeros on the closed disc, and let
`‖E'‖ ≤ ‖E‖` on the circle. Then `E − E'` has at most `κ` zeros in the open disc, unless it
vanishes identically there.

So every splitting has its defect certified by sizes in a height window: one circle in the window
suffices, with no hypothesis on a half-plane. At `κ = 0` the disc is free of zeros
(`ne_zero_of_norm_le_on_sphere`).

There is no winding number in the proof. The disc is carried onto the half-plane `Re s > ½` by
`s ↦ (s − 1)/s`; the quotient `E'/E` times the Blaschke product of the disc at `W` is a Schur
function by the maximum principle, the zeros of `E − E'` are its agreements with a Blaschke product
of degree `κ`, and a Schur function meets such a product in at most `κ` points
(`InfiniteRankPurityTheory.encard_agreements_le`).
-/

open Complex Metric Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

open GaloisForLFunctions.InfiniteRankPurityTheory

/-! ### The unit disc and the half-plane -/

theorem one_mem_rightHalf : (1 : ℂ) ∈ rightHalf := by
  show (1 : ℝ) / 2 < (1 : ℂ).re
  rw [one_re]
  norm_num

theorem defectFactor_one (s : ℂ) : defectFactor 1 s = (s - 1) / s := by
  unfold defectFactor
  rw [map_one, sub_self, sub_zero]

theorem defectInv_one (ζ : ℂ) : defectInv 1 ζ = 1 / (1 - ζ) := by
  unfold defectInv
  rw [map_one, sub_self, mul_zero, sub_zero]

theorem ne_zero_of_mem_rightHalf {s : ℂ} (hs : s ∈ rightHalf) : s ≠ 0 := fun h => by
  have h' : (1 : ℝ) / 2 < s.re := hs
  rw [h, zero_re] at h'
  linarith

theorem one_sub_ne_zero_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 :=
  one_sub_ne_zero_of_mem_ball (mem_ball_zero_iff.mpr hw)

/-- The unimodular constant `(1 − w)/(1 − w̄)`. -/
theorem norm_one_sub_div_conj {w : ℂ} (hw : ‖w‖ < 1) :
    ‖(1 - w) / (1 - (starRingEnd ℂ) w)‖ = 1 := by
  have h : 1 - (starRingEnd ℂ) w = (starRingEnd ℂ) (1 - w) := by rw [map_sub, map_one]
  rw [norm_div, h, RCLike.norm_conj, div_self]
  exact norm_ne_zero_iff.mpr (one_sub_ne_zero_of_norm_lt_one hw)

/-- **A Blaschke factor of the disc is a Blaschke factor of the half-plane.** Under
`s ↦ (s − 1)/s` the factor `(z − w)/(1 − w̄ z)` becomes a unimodular multiple of the factor of the
half-plane at `1/(1 − w)`. -/
theorem mobius_defectFactor_one {w : ℂ} (hw : ‖w‖ < 1) {s : ℂ} (hs : s ∈ rightHalf) :
    mobius w (defectFactor 1 s) =
      (1 - w) / (1 - (starRingEnd ℂ) w) * defectFactor (defectInv 1 w) s := by
  have hs0 := ne_zero_of_mem_rightHalf hs
  have h1 := one_sub_ne_zero_of_norm_lt_one hw
  have h2 : 1 - (starRingEnd ℂ) w ≠ 0 :=
    one_sub_ne_zero_of_norm_lt_one (by rwa [RCLike.norm_conj])
  have hz := mem_ball_zero_iff.mp (defectFactor_mem_ball one_mem_rightHalf hs)
  have h3 := mobius_denom_ne_zero hw hz.le
  rw [defectFactor_one] at h3
  have h3' : s - (starRingEnd ℂ) w * (s - 1) ≠ 0 := by
    intro h
    apply h3
    field_simp
    linear_combination h
  have hconj : (starRingEnd ℂ) (1 / (1 - w)) = 1 / (1 - (starRingEnd ℂ) w) := by
    rw [map_div₀, map_one, map_sub, map_one]
  unfold mobius
  rw [defectFactor_one, defectInv_one]
  unfold defectFactor
  rw [hconj]
  have h4 : s - (1 - 1 / (1 - (starRingEnd ℂ) w)) ≠ 0 := by
    intro h
    apply h3'
    field_simp at h
    linear_combination h
  field_simp
  ring

/-! ### Products over the defect -/

theorem differentiable_multiset_prod (W : Multiset ℂ) (f : ℂ → ℂ → ℂ)
    (hf : ∀ w, Differentiable ℂ (f w)) : Differentiable ℂ fun z => (W.map fun w => f w z).prod := by
  induction W using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (hf a).mul ih

/-- On the unit circle `‖1 − w̄ z‖ = ‖z − w‖`. -/
theorem norm_one_sub_conj_mul (w : ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖1 - (starRingEnd ℂ) w * z‖ = ‖z - w‖ := by
  have h : 1 - (starRingEnd ℂ) w * z = z * (starRingEnd ℂ) (z - w) := by
    rw [map_sub, mul_sub, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    push_cast
    ring
  rw [h, norm_mul, RCLike.norm_conj, hz, one_mul]

theorem norm_prod_one_sub_conj_mul (W : Multiset ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(W.map fun w => 1 - (starRingEnd ℂ) w * z).prod‖ = ‖(W.map fun w => z - w).prod‖ := by
  induction W using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [norm_mul, norm_mul, ih, norm_one_sub_conj_mul a hz]

/-- The Blaschke product of the disc at `W` times its denominators is the polynomial at `W`. -/
theorem prod_mobius_mul (W : Multiset ℂ) (hW : ∀ w ∈ W, ‖w‖ < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (W.map fun w => mobius w z).prod * (W.map fun w => 1 - (starRingEnd ℂ) w * z).prod =
      (W.map fun w => z - w).prod := by
  induction W using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    have ha := mobius_denom_ne_zero (hW a (Multiset.mem_cons_self a s)) hz
    have hs := ih fun w hw => hW w (Multiset.mem_cons_of_mem hw)
    have hm : mobius a z * (1 - (starRingEnd ℂ) a * z) = z - a := by
      unfold mobius
      rw [div_mul_cancel₀ _ ha]
    rw [← hs, ← hm]
    ring

/-- **The Blaschke product of the disc is a Blaschke product of the half-plane.** -/
theorem isBlaschke_disc (W : Multiset ℂ) (hW : ∀ w ∈ W, ‖w‖ < 1) :
    IsBlaschke (Multiset.card W) fun s => (W.map fun w => mobius w (defectFactor 1 s)).prod := by
  have hc : ‖(W.map fun w => (1 - w) / (1 - (starRingEnd ℂ) w)).prod‖ = 1 := by
    induction W using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [norm_mul, norm_one_sub_div_conj (hW a (Multiset.mem_cons_self a s)),
        ih fun w hw => hW w (Multiset.mem_cons_of_mem hw), mul_one]
  have hW' : ∀ v ∈ W.map (defectInv 1), v ∈ rightHalf := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hv
    exact defectInv_mem_rightHalf one_mem_rightHalf (mem_ball_zero_iff.mpr (hW w hw))
  have heq : ∀ s ∈ rightHalf, (W.map fun w => mobius w (defectFactor 1 s)).prod =
      (W.map fun w => (1 - w) / (1 - (starRingEnd ℂ) w)).prod *
        ((W.map (defectInv 1)).map fun v => defectFactor v s).prod := by
    intro s hs
    induction W using Multiset.induction_on with
    | empty => simp
    | cons a t ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [ih (fun w hw => hW w (Multiset.mem_cons_of_mem hw))
        (by
          have h := hc
          simp only [Multiset.map_cons, Multiset.prod_cons] at h
          rw [norm_mul, norm_one_sub_div_conj (hW a (Multiset.mem_cons_self a t)), one_mul] at h
          exact h)
        (fun v hv => hW' v (by
          rw [Multiset.map_cons]
          exact Multiset.mem_cons_of_mem hv)),
        mobius_defectFactor_one (hW a (Multiset.mem_cons_self a t)) hs]
      ring
  obtain ⟨N, ε, hN, hε, hne, hle, hBeq⟩ := isBlaschke_prod hc (W.map (defectInv 1)) hW'
  rw [Multiset.card_map] at hN
  exact ⟨N, ε, hN, hε, hne, hle, fun s hs => (heq s hs).trans (hBeq s hs)⟩

/-! ### The index law on the unit disc -/

/-- **The index law on the unit disc.** If `‖E'‖ ≤ ‖Π (z − w) · E₁‖` on the unit circle, with `W`
in the open disc and `E₁` without zeros on the closed disc, then `E'` and `Π (z − w) · E₁` agree
at at most `card W` points of the open disc, unless they agree identically. -/
theorem encard_agreements_unitDisc_le {E₁ E' : ℂ → ℂ} {W : Multiset ℂ} (hW : ∀ w ∈ W, ‖w‖ < 1)
    (hE₁ : DiffContOnCl ℂ E₁ (ball 0 1)) (hE₁0 : ∀ z ∈ closedBall (0 : ℂ) 1, E₁ z ≠ 0)
    (hE' : DiffContOnCl ℂ E' (ball 0 1))
    (hsize : ∀ z ∈ sphere (0 : ℂ) 1, ‖E' z‖ ≤ ‖(W.map fun w => z - w).prod * E₁ z‖)
    (hdiff : ∃ z ∈ ball (0 : ℂ) 1, E' z ≠ (W.map fun w => z - w).prod * E₁ z) :
    {z | z ∈ ball (0 : ℂ) 1 ∧ E' z = (W.map fun w => z - w).prod * E₁ z}.encard ≤
      Multiset.card W := by
  -- the denominators of the Blaschke product of the disc
  have hDd : Differentiable ℂ fun z => (W.map fun w => 1 - (starRingEnd ℂ) w * z).prod :=
    differentiable_multiset_prod W (fun w z => 1 - (starRingEnd ℂ) w * z) fun w => by fun_prop
  have hD0 : ∀ z ∈ closedBall (0 : ℂ) 1,
      (W.map fun w => 1 - (starRingEnd ℂ) w * z).prod ≠ 0 := by
    intro z hz
    refine Multiset.prod_ne_zero fun h0 => ?_
    obtain ⟨w, hw, hw0⟩ := Multiset.mem_map.mp h0
    exact mobius_denom_ne_zero (hW w hw) (mem_closedBall_zero_iff.mp hz) hw0
  have hcl : closure (ball (0 : ℂ) 1) = closedBall 0 1 := closure_ball 0 one_ne_zero
  -- the Schur function of the disc
  have hden : ∀ z ∈ closedBall (0 : ℂ) 1,
      E₁ z * (W.map fun w => 1 - (starRingEnd ℂ) w * z).prod ≠ 0 := fun z hz =>
    mul_ne_zero (hE₁0 z hz) (hD0 z hz)
  have hT : DiffContOnCl ℂ
      (fun z => E' z / (E₁ z * (W.map fun w => 1 - (starRingEnd ℂ) w * z).prod)) (ball 0 1) := by
    refine ⟨hE'.differentiableOn.div (hE₁.differentiableOn.mul hDd.differentiableOn)
      fun z hz => hden z (ball_subset_closedBall hz), ?_⟩
    rw [hcl]
    have c1 := hE'.continuousOn
    have c2 := hE₁.continuousOn
    rw [hcl] at c1 c2
    exact c1.div (c2.mul hDd.continuous.continuousOn) hden
  have hTb : ∀ z ∈ closedBall (0 : ℂ) 1,
      ‖E' z / (E₁ z * (W.map fun w => 1 - (starRingEnd ℂ) w * z).prod)‖ ≤ 1 := by
    intro z hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hT (fun y hy => ?_)
      (by rw [hcl]; exact hz)
    rw [frontier_ball (0 : ℂ) one_ne_zero] at hy
    have hy1 : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
    have hpos : 0 < ‖E₁ y * (W.map fun w => 1 - (starRingEnd ℂ) w * y).prod‖ :=
      norm_pos_iff.mpr (hden y (sphere_subset_closedBall hy))
    rw [norm_div, div_le_one hpos, norm_mul, norm_prod_one_sub_conj_mul W hy1, mul_comm,
      ← norm_mul]
    exact hsize y hy
  -- transport to the half-plane
  have hmaps : MapsTo (defectFactor 1) rightHalf (ball (0 : ℂ) 1) := fun s hs =>
    defectFactor_mem_ball one_mem_rightHalf hs
  have hφd : DifferentiableOn ℂ (defectFactor 1) rightHalf := by
    intro s hs
    have h : DifferentiableAt ℂ (fun s : ℂ => (s - 1) / s) s :=
      (differentiableAt_id.sub_const 1).div differentiableAt_id (ne_zero_of_mem_rightHalf hs)
    exact (h.congr_of_eventuallyEq (Eventually.of_forall fun t =>
      defectFactor_one t)).differentiableWithinAt
  have hθd : DifferentiableOn ℂ (fun s => E' (defectFactor 1 s) /
      (E₁ (defectFactor 1 s) *
        (W.map fun w => 1 - (starRingEnd ℂ) w * defectFactor 1 s).prod)) rightHalf :=
    hT.differentiableOn.comp hφd hmaps
  have hθb : ∀ s ∈ rightHalf, ‖E' (defectFactor 1 s) / (E₁ (defectFactor 1 s) *
      (W.map fun w => 1 - (starRingEnd ℂ) w * defectFactor 1 s).prod)‖ ≤ 1 := fun s hs =>
    hTb _ (ball_subset_closedBall (hmaps hs))
  -- agreements with the Blaschke product are the common values of `E'` and `E`
  have hkey : ∀ z ∈ ball (0 : ℂ) 1,
      (E' z / (E₁ z * (W.map fun w => 1 - (starRingEnd ℂ) w * z).prod) =
        (W.map fun w => mobius w z).prod ↔ E' z = (W.map fun w => z - w).prod * E₁ z) := by
    intro z hz
    have hzc := ball_subset_closedBall hz
    have hM := prod_mobius_mul W hW (mem_closedBall_zero_iff.mp hzc)
    rw [div_eq_iff (hden z hzc), ← hM]
    constructor <;> intro h <;> linear_combination h
  have hBl := isBlaschke_disc W hW
  have hdiff' : ∃ s ∈ rightHalf, E' (defectFactor 1 s) / (E₁ (defectFactor 1 s) *
      (W.map fun w => 1 - (starRingEnd ℂ) w * defectFactor 1 s).prod) ≠
        (W.map fun w => mobius w (defectFactor 1 s)).prod := by
    obtain ⟨z, hz, hne⟩ := hdiff
    refine ⟨defectInv 1 z, defectInv_mem_rightHalf one_mem_rightHalf hz, fun h => ?_⟩
    rw [defectFactor_defectInv one_mem_rightHalf hz] at h
    exact hne ((hkey z hz).mp h)
  have henc := encard_agreements_le hθd hθb hBl hdiff'
  have hsub : {z | z ∈ ball (0 : ℂ) 1 ∧ E' z = (W.map fun w => z - w).prod * E₁ z} ⊆
      defectFactor 1 '' {s | s ∈ rightHalf ∧ E' (defectFactor 1 s) / (E₁ (defectFactor 1 s) *
        (W.map fun w => 1 - (starRingEnd ℂ) w * defectFactor 1 s).prod) =
          (W.map fun w => mobius w (defectFactor 1 s)).prod} := by
    rintro z ⟨hz, hzeq⟩
    refine ⟨defectInv 1 z, ⟨defectInv_mem_rightHalf one_mem_rightHalf hz, ?_⟩,
      defectFactor_defectInv one_mem_rightHalf hz⟩
    rw [defectFactor_defectInv one_mem_rightHalf hz]
    exact (hkey z hz).mpr hzeq
  exact (Set.encard_mono hsub).trans ((Set.encard_image_le _ _).trans henc)

/-! ### Any disc -/

theorem prod_affine (W : Multiset ℂ) (c : ℂ) {R : ℝ} (hR : R ≠ 0) (ζ : ℂ) :
    (W.map fun w => c + (R : ℂ) * ζ - w).prod =
      (R : ℂ) ^ Multiset.card W * ((W.map fun w => (w - c) / (R : ℂ)).map fun v => ζ - v).prod := by
  have hRc : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR
  induction W using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    rw [ih, pow_succ]
    field_simp
    ring

/-- **Sizes on a circle certify the defect inside.** Let `E = Π_{w ∈ W} (z − w) · E₁` on a closed
disc, with `W` in the open disc and `E₁` without zeros on the closed disc, and let `‖E'‖ ≤ ‖E‖` on
the boundary circle. Then `E − E'` has at most `card W` zeros in the open disc, unless it vanishes
identically there. -/
theorem encard_zeros_le_of_norm_le_on_sphere {c : ℂ} {R : ℝ} (hR : 0 < R) {E₁ E' : ℂ → ℂ}
    {W : Multiset ℂ} (hW : ∀ w ∈ W, w ∈ ball c R) (hE₁ : DiffContOnCl ℂ E₁ (ball c R))
    (hE₁0 : ∀ z ∈ closedBall c R, E₁ z ≠ 0) (hE' : DiffContOnCl ℂ E' (ball c R))
    (hsize : ∀ z ∈ sphere c R, ‖E' z‖ ≤ ‖(W.map fun w => z - w).prod * E₁ z‖)
    (hdiff : ∃ z ∈ ball c R, (W.map fun w => z - w).prod * E₁ z - E' z ≠ 0) :
    {z | z ∈ ball c R ∧ (W.map fun w => z - w).prod * E₁ z - E' z = 0}.encard ≤
      Multiset.card W := by
  have hRc : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  -- the affine map of the unit disc onto the disc
  have hnorm : ∀ ζ : ℂ, ‖c + (R : ℂ) * ζ - c‖ = R * ‖ζ‖ := fun ζ => by
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
  have hmaps : MapsTo (fun ζ : ℂ => c + (R : ℂ) * ζ) (ball 0 1) (ball c R) := fun ζ hζ => by
    rw [mem_ball_iff_norm, hnorm]
    have := mem_ball_zero_iff.mp hζ
    nlinarith
  have hmapsc : ∀ ζ ∈ closedBall (0 : ℂ) 1, c + (R : ℂ) * ζ ∈ closedBall c R := fun ζ hζ => by
    rw [mem_closedBall_iff_norm, hnorm]
    have := mem_closedBall_zero_iff.mp hζ
    nlinarith
  have hmapss : ∀ ζ ∈ sphere (0 : ℂ) 1, c + (R : ℂ) * ζ ∈ sphere c R := fun ζ hζ => by
    rw [mem_sphere_iff_norm, hnorm, mem_sphere_zero_iff_norm.mp hζ, mul_one]
  have haff : DiffContOnCl ℂ (fun ζ : ℂ => c + (R : ℂ) * ζ) (ball 0 1) :=
    Differentiable.diffContOnCl (by fun_prop)
  have hW₀ : ∀ v ∈ W.map (fun w => (w - c) / (R : ℂ)), ‖v‖ < 1 := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hv
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, div_lt_one hR]
    exact mem_ball_iff_norm.mp (hW w hw)
  have hpow : ((R : ℂ)) ^ Multiset.card W ≠ 0 := pow_ne_zero _ hRc
  have hE₁c : DiffContOnCl ℂ (fun ζ => E₁ (c + (R : ℂ) * ζ)) (ball 0 1) := hE₁.comp haff hmaps
  have hE₁' : DiffContOnCl ℂ (fun ζ => (R : ℂ) ^ Multiset.card W * E₁ (c + (R : ℂ) * ζ))
      (ball 0 1) :=
    ⟨hE₁c.differentiableOn.const_mul _, continuousOn_const.mul hE₁c.continuousOn⟩
  have h := encard_agreements_unitDisc_le (W := W.map fun w => (w - c) / (R : ℂ))
    (E₁ := fun ζ => (R : ℂ) ^ Multiset.card W * E₁ (c + (R : ℂ) * ζ))
    (E' := fun ζ => E' (c + (R : ℂ) * ζ)) hW₀ hE₁'
    (fun ζ hζ => mul_ne_zero hpow (hE₁0 _ (hmapsc ζ hζ))) (hE'.comp haff hmaps)
    (fun ζ hζ => by
      have hs := hsize _ (hmapss ζ hζ)
      rw [prod_affine W c hR.ne'] at hs
      rw [← mul_assoc, mul_comm _ ((R : ℂ) ^ Multiset.card W)]
      exact hs)
    (by
      obtain ⟨z, hz, hne⟩ := hdiff
      refine ⟨(z - c) / (R : ℂ), ?_, fun heq => hne ?_⟩
      · rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le,
          div_lt_one hR]
        exact mem_ball_iff_norm.mp hz
      · have hback : c + (R : ℂ) * ((z - c) / (R : ℂ)) = z := by
          field_simp
          ring
        have hp := prod_affine W c hR.ne' ((z - c) / (R : ℂ))
        rw [hback] at hp
        rw [hback] at heq
        rw [hp, heq]
        ring)
  rw [Multiset.card_map] at h
  have hsub : {z | z ∈ ball c R ∧ (W.map fun w => z - w).prod * E₁ z - E' z = 0} ⊆
      (fun ζ : ℂ => c + (R : ℂ) * ζ) '' {ζ | ζ ∈ ball (0 : ℂ) 1 ∧ E' (c + (R : ℂ) * ζ) =
        ((W.map fun w => (w - c) / (R : ℂ)).map fun v => ζ - v).prod *
          ((R : ℂ) ^ Multiset.card W * E₁ (c + (R : ℂ) * ζ))} := by
    rintro z ⟨hz, hz0⟩
    have hback : c + (R : ℂ) * ((z - c) / (R : ℂ)) = z := by
      field_simp
      ring
    refine ⟨(z - c) / (R : ℂ), ⟨?_, ?_⟩, hback⟩
    · rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le,
        div_lt_one hR]
      exact mem_ball_iff_norm.mp hz
    · have hp := prod_affine W c hR.ne' ((z - c) / (R : ℂ))
      rw [hback] at hp
      rw [hback]
      have hz0' : E' z = (W.map fun w => z - w).prod * E₁ z := (sub_eq_zero.mp hz0).symm
      rw [hz0', hp]
      ring
  exact (Set.encard_mono hsub).trans ((Set.encard_image_le _ _).trans h)

/-- **Without defect the disc is free of zeros.** If `E` has no zero on a closed disc and
`‖E'‖ ≤ ‖E‖` on its boundary circle, then `E − E'` has no zero in the open disc, unless it
vanishes identically there. -/
theorem ne_zero_of_norm_le_on_sphere {c : ℂ} {R : ℝ} (hR : 0 < R) {E E' : ℂ → ℂ}
    (hE : DiffContOnCl ℂ E (ball c R)) (hE0 : ∀ z ∈ closedBall c R, E z ≠ 0)
    (hE' : DiffContOnCl ℂ E' (ball c R)) (hsize : ∀ z ∈ sphere c R, ‖E' z‖ ≤ ‖E z‖)
    (hdiff : ∃ z ∈ ball c R, E z - E' z ≠ 0) {z : ℂ} (hz : z ∈ ball c R) : E z - E' z ≠ 0 := by
  have h := encard_zeros_le_of_norm_le_on_sphere hR (W := 0) (E₁ := E) (E' := E')
    (fun w hw => absurd hw (Multiset.notMem_zero w)) hE hE0 hE'
    (fun y hy => by simpa using hsize y hy) (by simpa using hdiff)
  intro h0
  have hmem : z ∈ {z | z ∈ ball c R ∧
      ((0 : Multiset ℂ).map fun w => z - w).prod * E z - E' z = 0} := ⟨hz, by simpa using h0⟩
  rw [Multiset.card_zero, Nat.cast_zero, nonpos_iff_eq_zero, Set.encard_eq_zero] at h
  rw [h] at hmem
  exact hmem

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
