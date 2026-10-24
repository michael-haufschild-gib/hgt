import GaloisForLFunctions.RHTower.DeBruijnNonrealCountRightLimit
import GaloisForLFunctions.RHTower.DeBruijnNewmanStrictBound
import GaloisForLFunctions.RHTower.KiKimLeeSimpleZeros
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.HTGeometry.HermiteSignChanges

/-!
# The collision law of the de Bruijn–Newman flow

Let `N(t)` be the number of nonreal zeros of `H_t`, with multiplicity (`nonrealZeroCount`). It is
finite for `t > 0` (Ki–Kim–Lee), nonincreasing, right-continuous, and `0` from `t = 1/8` on. This
module computes its jumps exactly.

* **Backward local count** (`exists_ball_nonreal_count_backward`). If `x₀` is a real zero of order
  `k` of `H_t`, then for `s` slightly below `t` the nonreal zeros of `H_s` near `x₀` have total
  multiplicity exactly `k − k mod 2`. At the parabolic scale
  `H_{t−q²}(x₀ + qσ) = (a/k!) q^k P_k(σ) + O(q^{k+1})` with `P_k = e^{D²}σ^k`, and
  `P_k(iy) = i^k Q_k(y)` with `Q_k` the forward heat polynomial, whose `k` roots are real and
  simple. So the roots of `P_k` are `k` distinct points of the imaginary axis, and every one of
  them off the origin carries a nonreal zero of `H_{t−q²}` (`exists_nonreal_zeros_backward`);
  nonreal zeros in a disc centred on the axis pair off under conjugation, so their multiplicity is
  even (`even_sum_zeroMult_nonreal`), and at most `k`.
* **Jump law** (`exists_left_nonrealZeroCount`). For `0 < t ≤ 1/8`, just before `t`,
  `N(s) = N(t) + C(t)`, where the **collision mass** `C(t) = Σ 2⌊m/2⌋` runs over the finitely many
  real multiple zeros of `H_t` (`collisionMass`). A collision of multiplicity `m` lands exactly
  `2⌊m/2⌋` nonreal zeros on the real axis.
* **Global law** (`nonrealZeroCount_eq_sum_collisionMass`). For `0 < t ≤ 1/8` the collision times in
  `(t, 1/8]` are finitely many and `N(t)` is the total collision mass after `t`.

This is the collision-transfer law of `HTGeometry.HorizontalCharge` made global: off-line charge is
converted into multiplicity charge at collisions, and nothing else changes the nonreal count.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

/-! ## The roots of the backward model -/

/-- On the imaginary axis the backward model is the forward heat polynomial:
`P_k(ix) = i^k Q_k(x)`. -/
theorem heatModel_I_mul (k : ℕ) (x : ℝ) :
    heatModel k (I * x) = I ^ k * (heatPoly k x : ℂ) := by
  simp only [heatModel, heatPoly]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finset.mem_range] at hm
  have hI : I ^ k = I ^ (k - 2 * m) * (-1) ^ m := by
    rw [show (-1 : ℂ) ^ m = I ^ (2 * m) by rw [pow_mul, I_sq], ← pow_add,
      show k - 2 * m + 2 * m = k by omega]
  have hsq : ((-1 : ℂ)) ^ m * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
  rw [mul_pow, hI]
  linear_combination (-((k.factorial : ℂ) / ((m.factorial : ℂ) * ((k - 2 * m).factorial : ℂ)) *
    I ^ (k - 2 * m) * (x : ℂ) ^ (k - 2 * m))) * hsq

/-- `Q_k(0) ≠ 0` for even `k`: only the constant term survives. -/
theorem heatPoly_zero_ne_zero {k : ℕ} (hk : Even k) : heatPoly k 0 ≠ 0 := by
  obtain ⟨j, rfl⟩ := hk
  rw [heatPoly, Finset.sum_eq_single j
    (fun m hm hmj => by rw [Finset.mem_range] at hm; rw [zero_pow (by omega), mul_zero])
    (fun hj => absurd (Finset.mem_range.mpr (by omega)) hj)]
  rw [show j + j - 2 * j = 0 by omega, pow_zero, mul_one, mul_div_assoc]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)

/-- The roots of `P_k` off the real axis: `i√2 y` for the nonzero roots `y` of `Heₖ`. -/
def offAxisModelRoots (k : ℕ) : Finset ℂ :=
  ((realHermite k).roots.toFinset.filter (fun y => y ≠ 0)).image
    (fun y : ℝ => I * ((Real.sqrt 2 * y : ℝ) : ℂ))

theorem heatModel_eq_zero_of_mem_offAxisModelRoots {k : ℕ} {τ : ℂ}
    (hτ : τ ∈ offAxisModelRoots k) : heatModel k τ = 0 := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hτ
  have hroot : (realHermite k).IsRoot y := (Polynomial.mem_roots (realHermite_ne_zero k)).mp
    (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hy).1)
  rw [heatModel_I_mul, eval_heatPoly_eq,
    mul_div_cancel_left₀ _ (by positivity : Real.sqrt 2 ≠ 0), hroot.eq_zero]
  simp

theorem im_ne_zero_of_mem_offAxisModelRoots {k : ℕ} {τ : ℂ} (hτ : τ ∈ offAxisModelRoots k) :
    τ.im ≠ 0 := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hτ
  have hy0 := (Finset.mem_filter.mp hy).2
  simp only [mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul, zero_add]
  exact mul_ne_zero (by positivity) hy0

/-- `P_k` has at least `k − k mod 2` distinct roots off the real axis. -/
theorem card_offAxisModelRoots (k : ℕ) : k - k % 2 ≤ (offAxisModelRoots k).card := by
  classical
  obtain ⟨hnd, hcard⟩ := realHermite_roots_nodup_card k
  set R := (realHermite k).roots.toFinset with hR
  have hRk : R.card = k := by rw [hR, Multiset.toFinset_card_of_nodup hnd, hcard]
  have hinj : Function.Injective (fun y : ℝ => I * ((Real.sqrt 2 * y : ℝ) : ℂ)) := by
    intro a b h
    have h' := Complex.ofReal_injective (mul_left_cancel₀ I_ne_zero h)
    exact mul_left_cancel₀ (by positivity : Real.sqrt 2 ≠ 0) h'
  rw [offAxisModelRoots, Finset.card_image_of_injective _ hinj]
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := R) (fun y => y ≠ 0)
  have hzero : (R.filter (fun y => ¬ y ≠ 0)).card ≤ k % 2 := by
    rcases Nat.even_or_odd k with hk | hk
    · rw [Nat.even_iff.mp hk, Nat.le_zero, Finset.card_eq_zero]
      refine Finset.eq_empty_of_forall_notMem fun y hy => ?_
      obtain ⟨hyR, hy0⟩ := Finset.mem_filter.mp hy
      rw [not_not] at hy0
      subst hy0
      have hroot : (realHermite k).IsRoot 0 := (Polynomial.mem_roots (realHermite_ne_zero k)).mp
        (Multiset.mem_toFinset.mp hyR)
      apply heatPoly_zero_ne_zero hk
      rw [eval_heatPoly_eq, zero_div, hroot.eq_zero, mul_zero]
    · rw [Nat.odd_iff.mp hk]
      refine Finset.card_le_one.mpr fun a ha b hb => ?_
      rw [not_not.mp (Finset.mem_filter.mp ha).2, not_not.mp (Finset.mem_filter.mp hb).2]
  omega

/-! ## Zeros shed by a real zero, backward in time -/

/-- A positive lower bound for a positive function on a finite set. -/
theorem exists_pos_le_finset_of_pos {α : Type*} (T : Finset α) {g : α → ℝ}
    (hg : ∀ a ∈ T, 0 < g a) : ∃ m, 0 < m ∧ ∀ a ∈ T, m ≤ g a := by
  rcases T.eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun a ha => by simp [he] at ha⟩
  · exact ⟨T.inf' hne g, (Finset.lt_inf'_iff hne).mpr hg, fun a ha => Finset.inf'_le _ ha⟩

/-- **Zeros shed backward by a real zero.** Let `x₀` be a real zero of order `k` of `H_s`,
`s > 0`. There are `S > 0` and `q₁ > 0` with `q₁² < s` such that for `0 < q ≤ q₁` the function
`H_{s−q²}` has at least `k − k mod 2` distinct nonreal zeros within `qS` of `x₀`: one near
`x₀ + qτ` for each off-axis root `τ` of `P_k`, found by the minimum modulus principle. -/
theorem exists_nonreal_zeros_backward {s : ℝ} (hs : 0 < s) {x₀ : ℝ} {k : ℕ}
    (hvan : ∀ i < k, iteratedDeriv i (riemannHeat s) x₀ = 0)
    (ha : iteratedDeriv k (riemannHeat s) x₀ ≠ 0) :
    ∃ S, 0 < S ∧ ∃ q₁, 0 < q₁ ∧ q₁ ^ 2 < s ∧ ∀ q, 0 < q → q ≤ q₁ →
      ∃ W : Finset ℂ, k - k % 2 ≤ W.card ∧ ∀ w ∈ W,
        riemannHeat (s - q ^ 2) w = 0 ∧ w.im ≠ 0 ∧ ‖w - x₀‖ < q * S := by
  classical
  set H := riemannHeat s with hH
  set T := offAxisModelRoots k with hT
  have hTroot : ∀ τ ∈ T, heatModel k τ = 0 := fun τ hτ =>
    heatModel_eq_zero_of_mem_offAxisModelRoots hτ
  have hTim : ∀ τ ∈ T, τ.im ≠ 0 := fun τ hτ => im_ne_zero_of_mem_offAxisModelRoots hτ
  obtain ⟨d, hd, hdsep⟩ := exists_pos_sep T
  -- a circle around each root on which the model is bounded below
  have hcirc : ∀ τ ∈ T, ∃ ρ δ : ℝ, 0 < ρ ∧ ρ ≤ min (d / 3) (|τ.im| / 2) ∧ 0 < δ ∧
      ∀ σ ∈ sphere τ ρ, δ ≤ ‖heatModel k σ‖ := fun τ hτ =>
    exists_sphere_heatModel_lower k τ
      (lt_min (by positivity) (by have := abs_pos.mpr (hTim τ hτ); positivity))
  choose! ρ δ hρ hρε hδ hsph using hcirc
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ := exists_pos_le_finset_of_pos T hδ
  set S := ∑ τ ∈ T, (‖τ‖ + ρ τ) + 1 with hS
  have hnn : ∀ τ ∈ T, 0 ≤ ‖τ‖ + ρ τ := fun τ hτ => add_nonneg (norm_nonneg τ) (hρ τ hτ).le
  have hS0 : 0 < S := by have := Finset.sum_nonneg hnn; linarith
  have hτS : ∀ τ ∈ T, ‖τ‖ + ρ τ + 1 ≤ S := by
    intro τ hτ
    have := Finset.single_le_sum hnn hτ
    linarith
  obtain ⟨C, q₀, hq₀, hmodel⟩ := exists_norm_riemannHeat_sub_heatModel_le hs.le hvan hS0.le
  set A := ‖iteratedDeriv k H x₀‖ / (k.factorial : ℝ)
  have hA : 0 < A := div_pos (norm_pos_iff.mpr ha) (by exact_mod_cast Nat.factorial_pos k)
  set q₁ := min (min q₀ 1) (min (s / 2) (A * δ₀ / (4 * (|C| + 1))))
  have hq₁ : 0 < q₁ := lt_min (lt_min hq₀ one_pos) (lt_min (by positivity) (by positivity))
  have hq₁1 : q₁ ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hq₁s : q₁ ≤ s / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hq₁sq : q₁ ^ 2 < s := by nlinarith
  refine ⟨S, hS0, q₁, hq₁, hq₁sq, fun q hq hqq => ?_⟩
  have hqq₀ : q ≤ q₀ := hqq.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hq1 : q ≤ 1 := hqq.trans hq₁1
  have hqC : q ≤ A * δ₀ / (4 * (|C| + 1)) :=
    hqq.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hq2s : q ^ 2 < s := by nlinarith
  -- the error is below half the model on every circle
  have hCq : C * q ^ (k + 1) < A * δ₀ * q ^ k / 2 := by
    have hqk : 0 < q ^ k := pow_pos hq k
    have h1 : C * q ≤ |C| * q := mul_le_mul_of_nonneg_right (le_abs_self C) hq.le
    have h2 : |C| * q < A * δ₀ / 2 := by
      have : |C| * q ≤ |C| * (A * δ₀ / (4 * (|C| + 1))) :=
        mul_le_mul_of_nonneg_left hqC (abs_nonneg C)
      have h3 : |C| * (A * δ₀ / (4 * (|C| + 1))) < A * δ₀ / 2 := by
        rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [mul_pos hA hδ₀, abs_nonneg C]
      linarith
    calc C * q ^ (k + 1) = (C * q) * q ^ k := by ring
      _ ≤ (|C| * q) * q ^ k := mul_le_mul_of_nonneg_right h1 hqk.le
      _ < (A * δ₀ / 2) * q ^ k := mul_lt_mul_of_pos_right h2 hqk
      _ = A * δ₀ * q ^ k / 2 := by ring
  set f : ℂ → ℂ := fun σ => riemannHeat (s - q ^ 2) ((x₀ : ℂ) + q * σ) with hf
  have hfd : Differentiable ℂ f := by
    have := differentiable_riemannHeat (t := s - q ^ 2) (by linarith)
    simp only [hf]
    fun_prop
  have hnormA : ‖iteratedDeriv k H x₀ / (k.factorial : ℂ) * (q : ℂ) ^ k‖ = A * q ^ k := by
    rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hq]
  -- a zero of `f` inside each circle
  have hzero : ∀ τ ∈ T, ∃ σ ∈ ball τ (ρ τ), f σ = 0 := by
    intro τ hτ
    have hmain : ∀ σ : ℂ, ‖σ‖ ≤ S →
        ‖f σ - iteratedDeriv k H x₀ / (k.factorial : ℂ) * (q : ℂ) ^ k * heatModel k σ‖ ≤
          C * q ^ (k + 1) := fun σ hσ => hmodel q hq.le hqq₀ hq2s.le σ hσ
    have hcentre : ‖f τ‖ ≤ C * q ^ (k + 1) := by
      have := hmain τ (by linarith [hτS τ hτ, hρ τ hτ])
      rwa [hTroot τ hτ, mul_zero, sub_zero] at this
    have hsphere : ∀ σ ∈ sphere τ (ρ τ), ‖f τ‖ < ‖f σ‖ := by
      intro σ hσ
      have hσn : ‖σ‖ ≤ S := by
        have := norm_le_norm_add_norm_sub' σ τ
        rw [← dist_eq_norm, mem_sphere.mp hσ] at this
        linarith [hτS τ hτ]
      have h1 := hmain σ hσn
      have h2 := (hδ₀le τ hτ).trans (hsph τ hτ σ hσ)
      have h3 := norm_sub_norm_le
        (iteratedDeriv k H x₀ / (k.factorial : ℂ) * (q : ℂ) ^ k * heatModel k σ) (f σ)
      rw [norm_sub_rev, norm_mul, hnormA] at h3
      have h4 : A * q ^ k * δ₀ ≤ A * q ^ k * ‖heatModel k σ‖ :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      nlinarith
    exact exists_zero_of_norm_lt_sphere hfd (hρ τ hτ) hsphere
  choose! σ hσball hσzero using hzero
  refine ⟨T.image (fun τ => (x₀ : ℂ) + q * σ τ), ?_, fun w hw => ?_⟩
  · rw [Finset.card_image_of_injOn]
    · exact card_offAxisModelRoots k
    · intro τ hτ τ' hτ' hττ'
      by_contra hne
      have h1 := hdsep τ hτ τ' hτ' hne
      have h2 : σ τ = σ τ' :=
        mul_left_cancel₀ (by exact_mod_cast hq.ne') (add_left_cancel hττ')
      have hb1 := mem_ball.mp (hσball τ hτ)
      have hb2 := mem_ball.mp (hσball τ' hτ')
      rw [h2] at hb1
      have htri : dist τ τ' ≤ dist τ (σ τ') + dist (σ τ') τ' := dist_triangle _ _ _
      rw [dist_comm τ] at htri
      have hr1 := (hρε τ hτ).trans (min_le_left _ _)
      have hr2 := (hρε τ' hτ').trans (min_le_left _ _)
      linarith
  · obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨hσzero τ hτ, ?_, ?_⟩
    · have hb := mem_ball_iff_norm.mp (hσball τ hτ)
      have him := (Complex.abs_im_le_norm (σ τ - τ)).trans_lt hb
      rw [Complex.sub_im] at him
      have hr := (hρε τ hτ).trans (min_le_right _ _)
      have hτim := abs_pos.mpr (hTim τ hτ)
      have hσim : (σ τ).im ≠ 0 := by
        intro h0
        rw [h0, zero_sub, abs_neg] at him
        linarith
      have hwim : ((x₀ : ℂ) + q * σ τ).im = q * (σ τ).im := by simp
      rw [hwim]
      exact mul_ne_zero hq.ne' hσim
    · rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
      have hσn : ‖σ τ‖ < ‖τ‖ + ρ τ := by
        have := norm_le_norm_add_norm_sub' (σ τ) τ
        have hb := mem_ball_iff_norm.mp (hσball τ hτ)
        linarith
      have := hτS τ hτ
      exact mul_lt_mul_of_pos_left (by linarith) hq

/-! ## Conjugate pairing -/

/-- Multiplicities of `H_s` are invariant under conjugation. -/
theorem zeroMult_riemannHeat_conj {s : ℝ} (hs : 0 ≤ s) (z : ℂ) :
    zeroMult (riemannHeat s) ((starRingEnd ℂ) z) = zeroMult (riemannHeat s) z := by
  have hfun : (fun w => (starRingEnd ℂ) (riemannHeat s ((starRingEnd ℂ) w))) = riemannHeat s :=
    funext fun w => by rw [riemannHeat_conj hs, Complex.conj_conj]
  have h := analyticOrderAt_conj_conj (differentiable_riemannHeat hs) z
  rw [hfun] at h
  rw [zeroMult, zeroMult, h]

/-- **Conjugate pairing.** In a disc centred on the real axis, the nonreal zeros of `H_s` carry an
even total multiplicity. -/
theorem even_sum_zeroMult_nonreal {s : ℝ} (hs : 0 ≤ s) {x₀ r : ℝ} {Z : Finset ℂ}
    (hZz : ∀ z ∈ ball (x₀ : ℂ) r, riemannHeat s z = 0 ↔ z ∈ Z)
    (hZb : ∀ z ∈ Z, z ∈ ball (x₀ : ℂ) r) :
    Even (∑ z ∈ Z.filter (fun z => z.im ≠ 0), zeroMult (riemannHeat s) z) := by
  rw [← ZMod.natCast_eq_zero_iff_even, Nat.cast_sum]
  have hmem : ∀ z ∈ Z.filter (fun z => z.im ≠ 0),
      (starRingEnd ℂ) z ∈ Z.filter (fun z => z.im ≠ 0) := by
    intro z hz
    obtain ⟨hzZ, him⟩ := Finset.mem_filter.mp hz
    have hb := hZb z hzZ
    have hb' : (starRingEnd ℂ) z ∈ ball (x₀ : ℂ) r := by
      rw [mem_ball, dist_eq_norm] at hb ⊢
      rw [show (starRingEnd ℂ) z - x₀ = (starRingEnd ℂ) (z - x₀) by
        rw [map_sub, Complex.conj_ofReal], Complex.norm_conj]
      exact hb
    have h0 : riemannHeat s ((starRingEnd ℂ) z) = 0 := by
      rw [riemannHeat_conj hs, (hZz z hb).mpr hzZ, map_zero]
    exact Finset.mem_filter.mpr ⟨(hZz _ hb').mp h0, by simpa using him⟩
  refine Finset.sum_involution (fun z _ => (starRingEnd ℂ) z) (fun z _ => ?_)
    (fun z hz _ => ?_) hmem (fun z _ => Complex.conj_conj z)
  · rw [zeroMult_riemannHeat_conj hs]
    exact CharTwo.add_self_eq_zero _
  · intro h
    apply (Finset.mem_filter.mp hz).2
    have h' := congrArg Complex.im h
    simp only [Complex.conj_im] at h'
    linarith

/-! ## The backward local count -/

/-- **Backward local count.** Let `t > 0`, `x₀` real and `k` the multiplicity of `x₀` for `H_t`.
There is `r₀ > 0` such that for every `0 < r ≤ r₀` and every `s < t` close to `t`: `s > 0`, the
circle `|z − x₀| = r` is zero-free for `H_s`, and the nonreal zeros of `H_s` in the disc carry
total multiplicity exactly `k − k mod 2`. -/
theorem exists_ball_nonreal_count_backward {t : ℝ} (ht : 0 < t) (x₀ : ℝ) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∃ δ > 0, ∀ s, t - δ < s → s < t →
      0 < s ∧ (∀ w ∈ sphere (x₀ : ℂ) r, riemannHeat s w ≠ 0) ∧
      ∀ Z : Finset ℂ, (∀ z ∈ ball (x₀ : ℂ) r, riemannHeat s z = 0 ↔ z ∈ Z) →
        (∀ z ∈ Z, z ∈ ball (x₀ : ℂ) r) →
        ∑ z ∈ Z.filter (fun z => z.im ≠ 0), zeroMult (riemannHeat s) z =
          zeroMult (riemannHeat t) x₀ - zeroMult (riemannHeat t) x₀ % 2 := by
  classical
  obtain ⟨r₀, hr₀, hstable⟩ := eventually_zeroSumBall_riemannHeat_eq ht (x₀ : ℂ)
  refine ⟨r₀, hr₀, fun r hr hrr₀ => ?_⟩
  obtain ⟨-, -, hev⟩ := hstable r hr hrr₀
  set k := zeroMult (riemannHeat t) x₀ with hk
  have han : AnalyticAt ℂ (riemannHeat t) x₀ := (differentiable_riemannHeat ht.le).analyticAt _
  have hord : analyticOrderAt (riemannHeat t) x₀ = (k : ℕ∞) := by
    rw [hk, zeroMult, ENat.coe_toNat (analyticOrderAt_riemannHeat_ne_top ht.le _)]
  obtain ⟨hvan, hka⟩ := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero han).mp hord
  obtain ⟨S, hS, q₁, hq₁, hq₁t, hshed⟩ := exists_nonreal_zeros_backward ht hvan hka
  obtain ⟨δ₁, hδ₁, hδ₁ev⟩ := Metric.eventually_nhds_iff.mp hev
  set q₂ := min q₁ (r / (2 * S)) with hq₂def
  have hq₂ : 0 < q₂ := lt_min hq₁ (by positivity)
  refine ⟨min δ₁ (q₂ ^ 2), lt_min hδ₁ (by positivity), fun s hts hst => ?_⟩
  have hδq : t - s < q₂ ^ 2 := by linarith [min_le_right δ₁ (q₂ ^ 2)]
  obtain ⟨hcs, hsph_s⟩ := hδ₁ev (y := s)
    (by rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith [min_le_left δ₁ (q₂ ^ 2)])
  set q := Real.sqrt (t - s) with hqdef
  have hq : 0 < q := Real.sqrt_pos.mpr (by linarith)
  have hqq : q ≤ q₂ := by
    rw [hqdef, Real.sqrt_le_left hq₂.le]
    exact hδq.le
  have hqs : t - q ^ 2 = s := by rw [hqdef, Real.sq_sqrt (by linarith)]; ring
  have hqq₁ : q ≤ q₁ := hqq.trans (min_le_left _ _)
  have hs0 : 0 < s := by
    have : q ^ 2 ≤ q₁ ^ 2 := pow_le_pow_left₀ hq.le hqq₁ 2
    linarith
  refine ⟨hs0, hsph_s, fun Z hZz hZb => ?_⟩
  -- the disc carries `k` zeros of `H_s`
  obtain ⟨Z', hZ'b, hZ'z, hZ's⟩ := exists_zeroSet_zeroSumBall hr (by linarith : r < 2 * r)
    isOpen_univ (subset_univ _) (differentiable_riemannHeat hs0.le).differentiableOn hsph_s
  have hZZ' : Z' = Z := by
    ext z
    constructor
    · intro hz
      have hb := hZ'b z hz
      exact (hZz z hb).mp ((hZ'z z hb).mpr hz)
    · intro hz
      have hb := hZb z hz
      exact (hZ'z z hb).mp ((hZz z hb).mpr hz)
  rw [hZZ', hcs] at hZ's
  have hsumZ : ∑ z ∈ Z, zeroMult (riemannHeat s) z = k := by
    have : ((∑ z ∈ Z, zeroMult (riemannHeat s) z : ℕ) : ℂ) = (k : ℂ) := by
      push_cast; exact hZ's.symm
    exact_mod_cast this
  -- the shed zeros lie in the disc and are nonreal
  obtain ⟨W, hWcard, hW⟩ := hshed q hq hqq₁
  rw [hqs] at hW
  have hqSr : q * S < r := by
    have h1 : q ≤ r / (2 * S) := hqq.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have hWsub : W ⊆ Z.filter (fun z => z.im ≠ 0) := by
    intro w hw
    obtain ⟨hw0, hwim, hwd⟩ := hW w hw
    have hwb : w ∈ ball (x₀ : ℂ) r := by
      rw [mem_ball, dist_eq_norm]; linarith
    exact Finset.mem_filter.mpr ⟨(hZz w hwb).mp hw0, hwim⟩
  have hlow : W.card ≤ ∑ z ∈ Z.filter (fun z => z.im ≠ 0), zeroMult (riemannHeat s) z := by
    rw [Finset.card_eq_sum_ones]
    refine (Finset.sum_le_sum fun w hw => one_le_zeroMult_riemannHeat hs0.le (hW w hw).1).trans
      (Finset.sum_le_sum_of_subset hWsub)
  have hup : ∑ z ∈ Z.filter (fun z => z.im ≠ 0), zeroMult (riemannHeat s) z ≤ k := by
    rw [← hsumZ]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  obtain ⟨j, hj⟩ := even_sum_zeroMult_nonreal hs0.le hZz hZb
  omega

end

end RHTower.DeBruijn
