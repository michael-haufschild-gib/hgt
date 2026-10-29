import GaloisForLFunctions.RHTower.DeBruijnCollisionJumpLaw

/-!
# Every local heat-zero cluster becomes simple immediately forward

The forward Hermite model has as many distinct roots as the multiplicity
of the original zero. A minimum-modulus argument produces one nearby
heat zero for each model root. Conservation of the local multiplicity
then exhausts the cluster and forces every future zero to be simple.
The collision center may be nonreal.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

private def forwardModelRoots (k : ℕ) : Finset ℂ :=
  (realHermite k).roots.toFinset.image (fun y : ℝ => ((Real.sqrt 2 * y : ℝ) : ℂ))

private theorem forwardModelRoots_card (k : ℕ) : (forwardModelRoots k).card = k := by
  classical
  obtain ⟨hnd, hcard⟩ := realHermite_roots_nodup_card k
  have hinj : Function.Injective (fun y : ℝ => ((Real.sqrt 2 * y : ℝ) : ℂ)) := by
    intro a b h
    exact mul_left_cancel₀ (by positivity : Real.sqrt 2 ≠ 0) (Complex.ofReal_injective h)
  rw [forwardModelRoots, Finset.card_image_of_injective _ hinj,
    Multiset.toFinset_card_of_nodup hnd, hcard]

private theorem heatModelFwd_zero_of_mem {k : ℕ} {τ : ℂ}
    (hτ : τ ∈ forwardModelRoots k) : heatModelFwd k τ = 0 := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hτ
  have hroot : (realHermite k).IsRoot y := (Polynomial.mem_roots (realHermite_ne_zero k)).mp
    (Multiset.mem_toFinset.mp hy)
  rw [heatModelFwd_ofReal, eval_heatPoly_eq,
    mul_div_cancel_left₀ _ (by positivity : Real.sqrt 2 ≠ 0), hroot.eq_zero, mul_zero,
    Complex.ofReal_zero]

private theorem heatModelFwd_I_ne_zero (k : ℕ) : heatModelFwd k I ≠ 0 := by
  have heq : heatModelFwd k I = I ^ k * heatModel k 1 := by
    simp only [heatModelFwd, heatModel, one_pow, mul_one, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := Finset.mem_range.mp hm
    have hI : I ^ k = I ^ (k - 2 * m) * (-1) ^ m := by
      rw [show (-1 : ℂ) ^ m = I ^ (2 * m) by rw [pow_mul, I_sq], ← pow_add,
        show k - 2 * m + 2 * m = k by omega]
    rw [hI]
    ring
  rw [heq]
  refine mul_ne_zero (pow_ne_zero _ I_ne_zero) ?_
  rw [heatModel_eq]
  simpa only [one_pow, one_mul, Complex.ofReal_one] using
    heatModelEven_eval_ofReal_ne_zero k (x := 1) zero_le_one

private theorem differentiable_heatModelFwd (k : ℕ) : Differentiable ℂ (heatModelFwd k) := by
  unfold heatModelFwd
  fun_prop

private theorem exists_sphere_heatModelFwd_lower (k : ℕ) (τ : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ δ : ℝ, 0 < ρ ∧ ρ ≤ ε ∧ 0 < δ ∧ ∀ σ ∈ sphere τ ρ, δ ≤ ‖heatModelFwd k σ‖ := by
  have han := (differentiable_heatModelFwd k).analyticAt τ
  rcases han.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hall := ((differentiable_heatModelFwd k).differentiableOn.analyticOnNhd
      isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ τ) h (mem_univ I)
    exact heatModelFwd_I_ne_zero k hall
  · obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.mem_nhdsWithin_iff.mp h
    let ρ := min (ρ₀ / 2) ε
    have hρ : 0 < ρ := lt_min (by positivity) hε
    have hne : ∀ σ ∈ sphere τ ρ, heatModelFwd k σ ≠ 0 := by
      intro σ hσ
      refine hball ⟨?_, ?_⟩
      · rw [mem_ball, mem_sphere.mp hσ]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith only [hρ₀])
      · intro hστ
        rw [mem_singleton_iff.mp hστ, mem_sphere, dist_self] at hσ
        linarith only [hσ, hρ]
    obtain ⟨σ₁, hσ₁, hmin⟩ := (isCompact_sphere τ ρ).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr hρ.le)
      (differentiable_heatModelFwd k).continuous.norm.continuousOn
    exact ⟨ρ, ‖heatModelFwd k σ₁‖, hρ, min_le_right _ _,
      norm_pos_iff.mpr (hne σ₁ hσ₁), fun σ hσ => hmin hσ⟩

/-- A zero of order `k` at an arbitrary complex center produces `k`
distinct nearby zeros at every sufficiently close later heat time. -/
theorem exists_distinct_riemannHeat_zeros_forward {s : ℝ} (hs : 0 ≤ s) {z₀ : ℂ} {k : ℕ}
    (hvan : ∀ i < k, iteratedDeriv i (riemannHeat s) z₀ = 0)
    (ha : iteratedDeriv k (riemannHeat s) z₀ ≠ 0) :
    ∃ S : ℝ, 0 < S ∧ ∃ q₁ : ℝ, 0 < q₁ ∧ ∀ q : ℝ, 0 < q → q ≤ q₁ →
      ∃ W : Finset ℂ, W.card = k ∧ ∀ w ∈ W,
        riemannHeat (s + q ^ 2) w = 0 ∧ ‖w - z₀‖ < q * S := by
  classical
  let T := forwardModelRoots k
  have hTroot : ∀ τ ∈ T, heatModelFwd k τ = 0 := fun _ hτ => heatModelFwd_zero_of_mem hτ
  obtain ⟨d, hd, hdsep⟩ := exists_pos_sep T
  have hcirc : ∀ τ ∈ T, ∃ ρ δ : ℝ, 0 < ρ ∧ ρ ≤ d / 3 ∧ 0 < δ ∧
      ∀ σ ∈ sphere τ ρ, δ ≤ ‖heatModelFwd k σ‖ :=
    fun τ _ => exists_sphere_heatModelFwd_lower k τ (by positivity)
  choose! ρ δ hρ hρd hδ hsph using hcirc
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ := exists_pos_le_finset_of_pos T hδ
  let S := (∑ τ ∈ T, (‖τ‖ + ρ τ)) + 1
  have hnn : ∀ τ ∈ T, 0 ≤ ‖τ‖ + ρ τ := fun τ hτ => add_nonneg (norm_nonneg τ) (hρ τ hτ).le
  have hS : 0 < S := by
    have h := Finset.sum_nonneg hnn
    dsimp only [S]
    linarith only [h]
  have hτS : ∀ τ ∈ T, ‖τ‖ + ρ τ + 1 ≤ S := by
    intro τ hτ
    have h := Finset.single_le_sum hnn hτ
    dsimp only [S]
    linarith only [h]
  obtain ⟨C, q₀, hq₀, hmodel⟩ := exists_norm_riemannHeat_sub_heatModelFwd_le hs hvan hS.le
  let A := ‖iteratedDeriv k (riemannHeat s) z₀‖ / (k.factorial : ℝ)
  have hA : 0 < A := div_pos (norm_pos_iff.mpr ha) (by exact_mod_cast Nat.factorial_pos k)
  let q₁ := min q₀ (A * δ₀ / (4 * (|C| + 1)))
  have hq₁ : 0 < q₁ := lt_min hq₀ (by positivity)
  refine ⟨S, hS, q₁, hq₁, ?_⟩
  intro q hq hqq
  have hqq₀ : q ≤ q₀ := hqq.trans (min_le_left _ _)
  have hqC : 4 * (|C| + 1) * q ≤ A * δ₀ := by
    have h := hqq.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith only [h]
  have hCq : C * q ^ (k + 1) < A * δ₀ * q ^ k / 2 := by
    have h1 : C * q ≤ |C| * q := mul_le_mul_of_nonneg_right (le_abs_self C) hq.le
    have h2 : 0 ≤ |C| * q := mul_nonneg (abs_nonneg C) hq.le
    have h3 : C * q < A * δ₀ / 2 := by nlinarith only [h1, h2, hqC, hq]
    calc
      C * q ^ (k + 1) = (C * q) * q ^ k := by ring
      _ < (A * δ₀ / 2) * q ^ k := mul_lt_mul_of_pos_right h3 (pow_pos hq k)
      _ = _ := by ring
  let f : ℂ → ℂ := fun σ => riemannHeat (s + q ^ 2) (z₀ + q * σ)
  have hfd : Differentiable ℂ f := by
    have hh := differentiable_riemannHeat (t := s + q ^ 2) (by positivity)
    dsimp only [f]
    fun_prop
  have hnormA : ‖iteratedDeriv k (riemannHeat s) z₀ / (k.factorial : ℂ) * (q : ℂ) ^ k‖ =
      A * q ^ k := by
    rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hq]
  have hzero : ∀ τ ∈ T, ∃ σ ∈ ball τ (ρ τ), f σ = 0 := by
    intro τ hτ
    have hmain : ∀ σ : ℂ, ‖σ‖ ≤ S →
        ‖f σ - iteratedDeriv k (riemannHeat s) z₀ / (k.factorial : ℂ) *
          (q : ℂ) ^ k * heatModelFwd k σ‖ ≤ C * q ^ (k + 1) :=
      fun σ hσ => hmodel q hq.le hqq₀ σ hσ
    have hcentre : ‖f τ‖ ≤ C * q ^ (k + 1) := by
      have h := hmain τ (by linarith only [hτS τ hτ, hρ τ hτ])
      rwa [hTroot τ hτ, mul_zero, sub_zero] at h
    have hsphere : ∀ σ ∈ sphere τ (ρ τ), ‖f τ‖ < ‖f σ‖ := by
      intro σ hσ
      have hσn : ‖σ‖ ≤ S := by
        have h := norm_le_norm_add_norm_sub' σ τ
        rw [← dist_eq_norm, mem_sphere.mp hσ] at h
        linarith only [h, hτS τ hτ]
      have h1 := hmain σ hσn
      have h2 := (hδ₀le τ hτ).trans (hsph τ hτ σ hσ)
      have h3 := norm_sub_norm_le
        (iteratedDeriv k (riemannHeat s) z₀ / (k.factorial : ℂ) * (q : ℂ) ^ k * heatModelFwd k σ)
        (f σ)
      rw [norm_sub_rev, norm_mul, hnormA] at h3
      have h4 : A * q ^ k * δ₀ ≤ A * q ^ k * ‖heatModelFwd k σ‖ :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      nlinarith only [hcentre, h1, h3, h4, hCq]
    exact exists_zero_of_norm_lt_sphere hfd (hρ τ hτ) hsphere
  choose! σ hσball hσzero using hzero
  refine ⟨T.image (fun τ => z₀ + q * σ τ), ?_, ?_⟩
  · rw [Finset.card_image_of_injOn]
    · exact forwardModelRoots_card k
    · intro τ hτ τ' hτ' hττ'
      by_contra hne
      have h1 := hdsep τ hτ τ' hτ' hne
      have h2 : σ τ = σ τ' :=
        mul_left_cancel₀ (by exact_mod_cast hq.ne') (add_left_cancel hττ')
      have hb1 := mem_ball.mp (hσball τ hτ)
      have hb2 := mem_ball.mp (hσball τ' hτ')
      rw [h2] at hb1
      have htri := dist_triangle τ (σ τ') τ'
      rw [dist_comm τ (σ τ')] at htri
      linarith only [h1, hb1, hb2, htri, hρd τ hτ, hρd τ' hτ', hd]
  · intro w hw
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨hσzero τ hτ, ?_⟩
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
    have hσn : ‖σ τ‖ < ‖τ‖ + ρ τ := by
      have h := norm_le_norm_add_norm_sub' (σ τ) τ
      have hb := mem_ball_iff_norm.mp (hσball τ hτ)
      linarith only [h, hb]
    exact mul_lt_mul_of_pos_left (by linarith only [hσn, hτS τ hτ]) hq

/-- Every isolating disk around an arbitrary point has only simple heat
zeros at all sufficiently close strictly later times. -/
theorem exists_ball_simple_riemannHeat_zeros_forward {t : ℝ} (ht : 0 < t) (z₀ : ℂ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, t < s → s < t + δ →
        ∀ w ∈ ball z₀ r, riemannHeat s w = 0 →
          deriv (riemannHeat s) w ≠ 0 ∧ zeroMult (riemannHeat s) w = 1 := by
  classical
  obtain ⟨r₀, hr₀, hstable⟩ := eventually_zeroSumBall_riemannHeat_eq ht z₀
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr hrr₀
  obtain ⟨_, _, hev⟩ := hstable r hr hrr₀
  let k := zeroMult (riemannHeat t) z₀
  obtain ⟨hvan, hka⟩ := iteratedDeriv_zeroMult_data ht.le z₀
  obtain ⟨S, hS, q₁, hq₁, hdistinct⟩ := exists_distinct_riemannHeat_zeros_forward ht.le hvan hka
  obtain ⟨δ₁, hδ₁, hδ₁ev⟩ := Metric.eventually_nhds_iff.mp hev
  let q₂ := min q₁ (r / (2 * S))
  have hq₂ : 0 < q₂ := lt_min hq₁ (by positivity)
  refine ⟨min δ₁ (q₂ ^ 2), lt_min hδ₁ (by positivity), ?_⟩
  intro s hts hst w hw hw0
  have hsq : s - t < q₂ ^ 2 := by linarith only [hst, min_le_right δ₁ (q₂ ^ 2)]
  obtain ⟨hcs, hsph_s⟩ := hδ₁ev (y := s) (by
    rw [Real.dist_eq, abs_of_pos (by linarith only [hts])]
    linarith only [hst, min_le_left δ₁ (q₂ ^ 2)])
  let q := Real.sqrt (s - t)
  have hq : 0 < q := Real.sqrt_pos.mpr (by linarith only [hts])
  have hqq : q ≤ q₂ := by
    rw [Real.sqrt_le_left hq₂.le]
    exact hsq.le
  have hsq' : t + q ^ 2 = s := by
    rw [Real.sq_sqrt (by linarith only [hts])]
    ring
  obtain ⟨W, hWcard, hW⟩ := hdistinct q hq (hqq.trans (min_le_left _ _))
  rw [hsq'] at hW
  have hqS : q * S ≤ r / 2 := by
    have h := hqq.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith only [h]
  have hs0 : 0 ≤ s := (ht.trans hts).le
  obtain ⟨Z, hZball, hZzero, hsum⟩ := exists_zeroSet_zeroSumBall hr
    (by linarith only [hr] : r < 2 * r) isOpen_univ (subset_univ _)
    (differentiable_riemannHeat hs0).differentiableOn hsph_s
  rw [hcs] at hsum
  have hsumN : ∑ z ∈ Z, zeroMult (riemannHeat s) z = k := by
    have h : ((∑ z ∈ Z, zeroMult (riemannHeat s) z : ℕ) : ℂ) = (k : ℂ) := by
      push_cast
      exact hsum.symm
    exact_mod_cast h
  have hWZ : W ⊆ Z := by
    intro z hz
    obtain ⟨hz0, hzd⟩ := hW z hz
    have hzb : z ∈ ball z₀ r := by
      rw [mem_ball, dist_eq_norm]
      linarith only [hzd, hqS, hr]
    exact (hZzero z hzb).mp hz0
  have hcard : k ≤ Z.card := by
    change zeroMult (riemannHeat t) z₀ ≤ Z.card
    rw [← hWcard]
    exact Finset.card_le_card hWZ
  have hwZ : w ∈ Z := (hZzero w hw).mp hw0
  have hderiv : deriv (riemannHeat s) w ≠ 0 := by
    intro hd
    have hmult := two_le_zeroMult_riemannHeat hs0 hw0 hd
    have hsumErase := Finset.sum_erase_add Z (fun z => zeroMult (riemannHeat s) z) hwZ
    have hcardErase := Finset.card_erase_add_one hwZ
    have hrest : (Z.erase w).card ≤ ∑ z ∈ Z.erase w, zeroMult (riemannHeat s) z := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_le_sum fun z hz => one_le_zeroMult_riemannHeat hs0 ?_
      have hzZ := (Finset.mem_erase.mp hz).2
      exact (hZzero z (hZball z hzZ)).mpr hzZ
    omega
  exact ⟨hderiv, zeroMult_riemannHeat_eq_one hs0 hw0 hderiv⟩

end

end RHTower.DeBruijn
