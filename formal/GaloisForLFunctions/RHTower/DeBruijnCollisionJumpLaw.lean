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
* **Global law** (`nonrealZeroCount_eq_sum_collisionMass`). For every `t > 0` the collision times
  after `t` are finitely many (`finite_collisionTimes`) and `N(t)` is the total collision mass after
  `t` (`collisionMassAfter`). In particular RH holds iff the flow has no collision at any positive
  time (`riemannHypothesis_iff_forall_collisionMass_eq_zero`).

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
  rw [offAxisModelRoots, Finset.card_image_of_injective _ hinj, ← hR]
  have hsplit := Finset.card_filter_add_card_filter_not (s := R) (fun y => y ≠ 0)
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
      rw [dist_comm τ (σ τ')] at htri
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

/-! ## The collision mass -/

/-- The order data of `H_t` at a point: derivatives below the multiplicity vanish, the next does
not. -/
theorem iteratedDeriv_zeroMult_data {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    (∀ i < zeroMult (riemannHeat t) z, iteratedDeriv i (riemannHeat t) z = 0) ∧
      iteratedDeriv (zeroMult (riemannHeat t) z) (riemannHeat t) z ≠ 0 := by
  have han : AnalyticAt ℂ (riemannHeat t) z := (differentiable_riemannHeat ht).analyticAt _
  have hord : analyticOrderAt (riemannHeat t) z = (zeroMult (riemannHeat t) z : ℕ∞) := by
    rw [zeroMult, ENat.coe_toNat (analyticOrderAt_riemannHeat_ne_top ht _)]
  exact (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero han).mp hord

/-- A zero with vanishing derivative has multiplicity at least two. -/
theorem two_le_zeroMult_riemannHeat {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : riemannHeat t z = 0)
    (hd : deriv (riemannHeat t) z = 0) : 2 ≤ zeroMult (riemannHeat t) z := by
  have hne := (iteratedDeriv_zeroMult_data ht z).2
  by_contra h
  interval_cases hm : zeroMult (riemannHeat t) z
  · exact hne (by rw [iteratedDeriv_zero]; exact hz)
  · exact hne (by rw [iteratedDeriv_one]; exact hd)

/-- A zero with nonvanishing derivative is simple. -/
theorem zeroMult_riemannHeat_eq_one {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : riemannHeat t z = 0)
    (hd : deriv (riemannHeat t) z ≠ 0) : zeroMult (riemannHeat t) z = 1 := by
  have h1 := one_le_zeroMult_riemannHeat ht hz
  by_contra h
  exact hd (by
    rw [← iteratedDeriv_one]
    exact (iteratedDeriv_zeroMult_data ht z).1 1 (by omega))

/-- The real multiple zeros of `H_t`: finitely many for `0 < t ≤ 1/8` (Ki–Kim–Lee), and the empty
set otherwise. -/
def realMultipleZeros (t : ℝ) : Finset ℂ :=
  if h : 0 < t ∧ t ≤ 1 / 8 then
    (riemannHeat_nonreal_or_multiple_zeros_finite h.1 h.2).toFinset.filter (fun z => z.im = 0)
  else ∅

theorem mem_realMultipleZeros {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) {z : ℂ} :
    z ∈ realMultipleZeros t ↔
      riemannHeat t z = 0 ∧ z.im = 0 ∧ deriv (riemannHeat t) z = 0 := by
  rw [realMultipleZeros, dif_pos ⟨ht, ht8⟩, Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨h0, hor⟩, him⟩
    exact ⟨h0, him, hor.resolve_left (not_not.mpr him)⟩
  · rintro ⟨h0, him, hd⟩
    exact ⟨⟨h0, Or.inr hd⟩, him⟩

/-- From `t = 1/8` on all zeros are real and simple: no collisions. -/
theorem realMultipleZeros_eq_empty_of_eighth_le {t : ℝ} (ht : 1 / 8 ≤ t) :
    realMultipleZeros t = ∅ := by
  rcases eq_or_lt_of_le ht with h | h
  · subst h
    refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨h0, -, hd⟩ := (mem_realMultipleZeros (by norm_num) le_rfl).mp hz
    exact (riemannHeat_zeros_real_simple_of_eighth_le le_rfl h0).2 hd
  · rw [realMultipleZeros, dif_neg fun h' => absurd h'.2 (not_le.mpr h)]

/-- The **collision mass** of the de Bruijn–Newman flow at time `t`: `Σ (m − m mod 2) = Σ 2⌊m/2⌋`
over the real multiple zeros of `H_t`, `m` the multiplicity. -/
def collisionMass (t : ℝ) : ℕ :=
  ∑ z ∈ realMultipleZeros t, (zeroMult (riemannHeat t) z - zeroMult (riemannHeat t) z % 2)

theorem collisionMass_eq_zero_of_eighth_le {t : ℝ} (ht : 1 / 8 ≤ t) : collisionMass t = 0 := by
  rw [collisionMass, realMultipleZeros_eq_empty_of_eighth_le ht, Finset.sum_empty]

/-- The collision mass can be summed over any finite set of real zeros of `H_t` containing the
multiple ones: simple zeros contribute `0`. -/
theorem collisionMass_eq_sum_of_subset {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) {E : Finset ℂ}
    (hE : ∀ e ∈ E, riemannHeat t e = 0 ∧ e.im = 0) (hsub : realMultipleZeros t ⊆ E) :
    collisionMass t =
      ∑ e ∈ E, (zeroMult (riemannHeat t) e - zeroMult (riemannHeat t) e % 2) := by
  refine Finset.sum_subset hsub fun e he hne => ?_
  obtain ⟨h0, him⟩ := hE e he
  have hd : deriv (riemannHeat t) e ≠ 0 := fun hd =>
    hne ((mem_realMultipleZeros ht ht8).mpr ⟨h0, him, hd⟩)
  rw [zeroMult_riemannHeat_eq_one ht.le h0 hd]
  rfl

/-! ## The jump law -/

/-- **The jump law.** For `0 < t₁ ≤ 1/8`, just before `t₁` the nonreal count exceeds `N(t₁)` by the
collision mass: `N(s) = N(t₁) + C(t₁)` for `t₁ − δ < s < t₁`. Every zero of `H_s` near `t₁` lies in
a small disc around a zero of `H_{t₁}`; a disc around a nonreal zero holds only nonreal zeros, and a
disc around a real zero of multiplicity `m` holds exactly `m − m mod 2` nonreal ones. -/
theorem exists_left_nonrealZeroCount {t₁ : ℝ} (ht₁ : 0 < t₁) (ht₁8 : t₁ ≤ 1 / 8) :
    ∃ δ > 0, ∀ s, t₁ - δ < s → s < t₁ →
      nonrealZeroCount s = nonrealZeroCount t₁ + collisionMass t₁ := by
  classical
  -- (1) the nonreal zeros near `t₁` lie in a fixed disc
  obtain ⟨X₀, hX₀⟩ := exists_riemannHeat_zeros_real_uniform (t₀ := t₁ / 2) (by linarith)
  set X := max X₀ 0 + 1 with hXdef
  have hinside : ∀ t ∈ Icc (t₁ / 2) (1 / 8), ∀ z, riemannHeat t z = 0 → z.im ≠ 0 → ‖z‖ < X := by
    intro t htI z hz him
    have htpos : 0 < t := by linarith [htI.1]
    have hre : |z.re| < X₀ := lt_of_not_ge fun h => him (hX₀ t htI z hz h)
    have him2 := abs_im_le_half_of_riemannHeat_eq_zero htpos hz
    have h3 := Complex.norm_le_abs_re_add_abs_im z
    have hX : X₀ ≤ max X₀ 0 := le_max_left _ _
    linarith
  -- (2) a zero-free circle `|z| = R` with `X < R < X + 1`
  have han : AnalyticOnNhd ℂ (riemannHeat t₁) (closedBall 0 (X + 1)) := fun z _ =>
    (differentiable_riemannHeat ht₁.le).analyticAt z
  have hfin := finite_zeros_closedBall han (fun z _ h =>
    analyticOrderAt_riemannHeat_ne_top ht₁.le z (analyticOrderAt_eq_top.mpr h))
  obtain ⟨R, hRI, hRn⟩ := (Set.Ioo_infinite (by linarith : X < X + 1)).exists_notMem_finset
    (hfin.toFinset.image (fun z => ‖z‖))
  have hRX : X < R := hRI.1
  have hRpos : 0 < R := by have : 0 ≤ max X₀ 0 := le_max_right _ _; linarith
  have hsphR : ∀ w ∈ sphere (0 : ℂ) R, riemannHeat t₁ w ≠ 0 := by
    intro w hw h0
    rw [mem_sphere, dist_zero_right] at hw
    apply hRn
    refine Finset.mem_image.mpr ⟨w, ?_, hw⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨by rw [mem_closedBall, dist_zero_right]; linarith [hRI.2], h0⟩
  -- (3) the zeros of `H_{t₁}` in `|z| < R`
  set E := hfin.toFinset.filter (fun z => ‖z‖ < R) with hE
  have hmemE : ∀ z, z ∈ E ↔ riemannHeat t₁ z = 0 ∧ ‖z‖ < R := by
    intro z
    rw [hE, Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨-, h0⟩, hz⟩; exact ⟨h0, hz⟩
    · rintro ⟨h0, hz⟩
      exact ⟨⟨by rw [mem_closedBall, dist_zero_right]; linarith [hRI.2], h0⟩, hz⟩
  -- (4) radii
  choose ρ₀ hρ₀ hρ₀prop using fun e => eventually_zeroSumBall_riemannHeat_eq ht₁ e
  choose ρ₁ hρ₁ hρ₁prop using fun e : ℂ => exists_ball_nonreal_count_backward ht₁ e.re
  obtain ⟨d, hd, hdsep⟩ := exists_pos_sep E
  set A : ℂ → ℝ := fun e => min (min (ρ₀ e) (ρ₁ e)) (min (d / 3) ((R - ‖e‖) / 2)) with hAdef
  set r : ℂ → ℝ := fun e => if e.im = 0 then A e else min (A e) (|e.im| / 2) with hrdef
  have hrA : ∀ e, r e ≤ A e := by
    intro e; simp only [hrdef]; split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hApos : ∀ e ∈ E, 0 < A e := by
    intro e he
    have hR := ((hmemE e).mp he).2
    exact lt_min (lt_min (hρ₀ e) (hρ₁ e)) (lt_min (by positivity) (by linarith))
  have hrpos : ∀ e ∈ E, 0 < r e := by
    intro e he
    simp only [hrdef]
    split_ifs with h
    · exact hApos e he
    · exact lt_min (hApos e he) (by have := abs_pos.mpr h; linarith)
  have hr₀ : ∀ e, r e ≤ ρ₀ e := fun e =>
    (hrA e).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr₁ : ∀ e, r e ≤ ρ₁ e := fun e =>
    (hrA e).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrd : ∀ e, r e ≤ d / 3 := fun e =>
    (hrA e).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrR : ∀ e, r e ≤ (R - ‖e‖) / 2 := fun e =>
    (hrA e).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrim : ∀ e, e.im ≠ 0 → r e ≤ |e.im| / 2 := by
    intro e h; simp only [hrdef, if_neg h]; exact min_le_right _ _
  -- (5) geometry of the discs
  have hdisj : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → Disjoint (ball e (r e)) (ball e' (r e')) := by
    intro e he e' he' hne
    refine Set.disjoint_left.mpr fun w hw hw' => ?_
    have h1 := hdsep e he e' he' hne
    have h2 : dist e e' ≤ dist e w + dist w e' := dist_triangle _ _ _
    rw [mem_ball] at hw hw'
    rw [dist_comm] at hw
    linarith [hrd e, hrd e']
  have havoid : ∀ e, e.im ≠ 0 → ∀ w ∈ ball e (r e), w.im ≠ 0 := by
    intro e h w hw hw0
    have h1 : |(w - e).im| ≤ ‖w - e‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hw0, zero_sub, abs_neg] at h1
    rw [mem_ball, dist_eq_norm] at hw
    have := hrim e h
    have hpos := abs_pos.mpr h
    linarith
  have hinR : ∀ e ∈ E, ∀ w ∈ ball e (r e), w ∈ ball (0 : ℂ) R := by
    intro e he w hw
    have hR := ((hmemE e).mp he).2
    rw [mem_ball, dist_eq_norm] at hw
    rw [mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' w e
    linarith [hrR e]
  -- (6) counts near `t₁`
  have hbig := eventually_zeroSumBall_riemannHeat_eq_of_sphere ht₁ hRpos hsphR
  have hsmall : ∀ᶠ s in 𝓝 t₁, ∀ e ∈ E,
      zeroSumBall (riemannHeat s) e (r e) = (zeroMult (riemannHeat t₁) e : ℂ) ∧
        ∀ w ∈ sphere e (r e), riemannHeat s w ≠ 0 :=
    (Filter.eventually_all_finset E).mpr fun e he => (hρ₀prop e (r e) (hrpos e he) (hr₀ e)).2.2
  have hcountE : zeroSumBall (riemannHeat t₁) 0 R =
      ∑ e ∈ E, (zeroMult (riemannHeat t₁) e : ℂ) := by
    obtain ⟨Z, hZb, hZz, hZs⟩ := exists_zeroSet_zeroSumBall hRpos (by linarith : R < 2 * R)
      isOpen_univ (subset_univ _) (differentiable_riemannHeat ht₁.le).differentiableOn hsphR
    have hZE : Z = E := by
      ext z
      constructor
      · intro hz
        have hb := hZb z hz
        refine (hmemE z).mpr ⟨(hZz z hb).mpr hz, ?_⟩
        rwa [mem_ball, dist_zero_right] at hb
      · intro hz
        obtain ⟨h0, hR⟩ := (hmemE z).mp hz
        exact (hZz z (by rw [mem_ball, dist_zero_right]; exact hR)).mp h0
    rw [hZs, hZE]
  -- (7) the real discs: the backward local count
  have hreal : ∀ e ∈ E, e.im = 0 → ∃ δ > 0, ∀ s, t₁ - δ < s → s < t₁ →
      ∀ Z : Finset ℂ, (∀ z ∈ ball e (r e), riemannHeat s z = 0 ↔ z ∈ Z) →
        (∀ z ∈ Z, z ∈ ball e (r e)) →
        ∑ z ∈ Z.filter (fun z => z.im ≠ 0), zeroMult (riemannHeat s) z =
          zeroMult (riemannHeat t₁) e - zeroMult (riemannHeat t₁) e % 2 := by
    intro e he him
    obtain ⟨δ, hδ, h⟩ := hρ₁prop e (r e) (hrpos e he) (hr₁ e)
    have he' : ((e.re : ℝ) : ℂ) = e := Complex.ext (by simp) (by simp [him])
    rw [he'] at h
    exact ⟨δ, hδ, fun s h1 h2 => (h s h1 h2).2.2⟩
  choose! δr hδr hδrprop using hreal
  obtain ⟨δ₂, hδ₂, hδ₂le⟩ := exists_pos_le_finset_of_pos (E.filter (fun e => e.im = 0))
    (g := δr) fun e he => hδr e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
  obtain ⟨δ₀, hδ₀, hδ₀ev⟩ := Metric.eventually_nhds_iff.mp (hbig.and hsmall)
  set δ := min (min δ₀ δ₂) (t₁ / 2) with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hδ₀ hδ₂) (by linarith)
  set Enr := E.filter (fun e => e.im ≠ 0) with hEnr
  have hEnr_sub : ∀ e ∈ Enr, e ∈ E ∧ e.im ≠ 0 := fun e he => Finset.mem_filter.mp he
  -- the count at `t₁`
  have hN₁ : nonrealZeroCount t₁ = ∑ e ∈ Enr, zeroMult (riemannHeat t₁) e := by
    refine ((sum_le_nonrealZeroCount ht₁ (E := Enr) (r := r)
      (n := fun e => zeroMult (riemannHeat t₁) e)
      (fun e he => hrpos e (hEnr_sub e he).1)
      (fun e he => havoid e (hEnr_sub e he).2)
      (fun e he e' he' hne => hdisj e (hEnr_sub e he).1 e' (hEnr_sub e' he').1 hne)
      (fun e he => (hρ₀prop e (r e) (hrpos e (hEnr_sub e he).1) (hr₀ e)).1)
      (fun e he => (hρ₀prop e (r e) (hrpos e (hEnr_sub e he).1) (hr₀ e)).2.1)).2 ?_)
    intro w hw0 hwim
    have hwX := hinside t₁ ⟨by linarith, ht₁8⟩ w hw0 hwim
    refine ⟨w, Finset.mem_filter.mpr ⟨(hmemE w).mpr ⟨hw0, by linarith⟩, hwim⟩,
      mem_ball_self (hrpos w ((hmemE w).mpr ⟨hw0, by linarith⟩))⟩
  -- the collision mass is carried by the real zeros in `|z| < R`
  have hmultR : realMultipleZeros t₁ ⊆ E.filter (fun e => e.im = 0) := by
    intro z hz
    obtain ⟨h0, him, hdz⟩ := (mem_realMultipleZeros ht₁ ht₁8).mp hz
    have hz' : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [him])
    have hk2 : 2 ≤ zeroMult (riemannHeat t₁) ((z.re : ℝ) : ℂ) := by
      rw [hz']; exact two_le_zeroMult_riemannHeat ht₁.le h0 hdz
    obtain ⟨hvan, hka⟩ := iteratedDeriv_zeroMult_data ht₁.le ((z.re : ℝ) : ℂ)
    obtain ⟨S, hS, q₁, hq₁, hq₁t, hshed⟩ := exists_nonreal_zeros_backward ht₁ hvan hka
    set q := min q₁ (min (Real.sqrt (t₁ / 2)) ((R - X) / (2 * S))) with hqdef
    have hq : 0 < q := lt_min hq₁ (lt_min (Real.sqrt_pos.mpr (by linarith))
      (div_pos (by linarith) (by positivity)))
    obtain ⟨W, hWcard, hW⟩ := hshed q hq (min_le_left _ _)
    obtain ⟨w, hw⟩ : W.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨hw0, hwim, hwd⟩ := hW w hw
    have hq2 : q ^ 2 ≤ t₁ / 2 := by
      have h1 : q ≤ Real.sqrt (t₁ / 2) := (min_le_right _ _).trans (min_le_left _ _)
      calc q ^ 2 ≤ Real.sqrt (t₁ / 2) ^ 2 := pow_le_pow_left₀ hq.le h1 2
        _ = t₁ / 2 := Real.sq_sqrt (by linarith)
    have hwX := hinside (t₁ - q ^ 2) ⟨by linarith, by have := sq_nonneg q; linarith⟩ w hw0 hwim
    have hqS : q * S ≤ (R - X) / 2 := by
      have h1 : q ≤ (R - X) / (2 * S) := (min_le_right _ _).trans (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at h1
      linarith
    have hzw : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
      have := norm_le_norm_add_norm_sub' z w
      rwa [norm_sub_rev] at this
    rw [hz'] at hwd
    exact Finset.mem_filter.mpr ⟨(hmemE z).mpr ⟨h0, by linarith⟩, him⟩
  have hcoll : collisionMass t₁ = ∑ e ∈ E.filter (fun e => e.im = 0),
      (zeroMult (riemannHeat t₁) e - zeroMult (riemannHeat t₁) e % 2) :=
    collisionMass_eq_sum_of_subset ht₁ ht₁8 (fun e he =>
      ⟨((hmemE e).mp (Finset.mem_filter.mp he).1).1, (Finset.mem_filter.mp he).2⟩) hmultR
  refine ⟨δ, hδpos, fun s hts hst => ?_⟩
  have hsd : dist s t₁ < δ₀ := by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    have h1 : δ ≤ δ₀ := (min_le_left _ _).trans (min_le_left _ _)
    linarith
  obtain ⟨⟨hbs, hbsph⟩, hsm⟩ := hδ₀ev hsd
  have hs0 : 0 < s := by have : δ ≤ t₁ / 2 := min_le_right _ _; linarith
  have hsI : s ∈ Icc (t₁ / 2) (1 / 8) :=
    ⟨by have : δ ≤ t₁ / 2 := min_le_right _ _; linarith, by linarith⟩
  -- the zero sets of `H_s` in the large disc and in the small discs
  have hdiffs := differentiable_riemannHeat hs0.le
  obtain ⟨Zb, hZbb, hZbz, hZbs⟩ := exists_zeroSet_zeroSumBall hRpos (by linarith : R < 2 * R)
    isOpen_univ (subset_univ _) hdiffs.differentiableOn hbsph
  have hZe : ∀ e ∈ E, ∃ Z : Finset ℂ, (∀ ρ ∈ Z, ρ ∈ ball e (r e)) ∧
      (∀ z ∈ ball e (r e), riemannHeat s z = 0 ↔ z ∈ Z) ∧
      zeroSumBall (riemannHeat s) e (r e) = ∑ ρ ∈ Z, (zeroMult (riemannHeat s) ρ : ℂ) :=
    fun e he => exists_zeroSet_zeroSumBall (hrpos e he)
      (by linarith [hrpos e he] : r e < 2 * r e) isOpen_univ (subset_univ _)
      hdiffs.differentiableOn (hsm e he).2
  choose! W hWb hWz hWs using hZe
  have hWsub : ∀ e ∈ E, W e ⊆ Zb := by
    intro e he z hz
    have hb := hWb e he z hz
    exact (hZbz z (hinR e he z hb)).mp ((hWz e he z hb).mpr hz)
  have hWdisj : (E : Set ℂ).PairwiseDisjoint W := by
    intro e he e' he' hne
    refine Finset.disjoint_left.mpr fun z hz hz' => ?_
    exact (Set.disjoint_left.mp (hdisj e he e' he' hne)) (hWb e he z hz) (hWb e' he' z hz')
  have hsumN : ∑ z ∈ Zb, zeroMult (riemannHeat s) z =
      ∑ e ∈ E, ∑ z ∈ W e, zeroMult (riemannHeat s) z := by
    have h1 : ((∑ z ∈ Zb, zeroMult (riemannHeat s) z : ℕ) : ℂ) =
        ((∑ e ∈ E, ∑ z ∈ W e, zeroMult (riemannHeat s) z : ℕ) : ℂ) := by
      push_cast
      rw [← hZbs, hbs, hcountE]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [← hWs e he, (hsm e he).1]
    exact_mod_cast h1
  have hcov := subset_biUnion_of_sum_eq (fun z hz => one_le_zeroMult_riemannHeat hs0.le
    ((hZbz z (hZbb z hz)).mpr hz)) hWsub hWdisj hsumN
  -- the nonreal zeros of `H_s` are the nonreal points of the small discs
  have hF : (riemannHeat_nonreal_zeros_finite hs0).toFinset =
      (E.biUnion W).filter (fun z => z.im ≠ 0) := by
    ext w
    rw [Set.Finite.mem_toFinset, Finset.mem_filter]
    constructor
    · rintro ⟨hw0, hwim⟩
      have hwX := hinside s hsI w hw0 hwim
      have hwb : w ∈ ball (0 : ℂ) R := by rw [mem_ball, dist_zero_right]; linarith
      exact ⟨hcov ((hZbz w hwb).mp hw0), hwim⟩
    · rintro ⟨hw, hwim⟩
      obtain ⟨e, he, hwe⟩ := Finset.mem_biUnion.mp hw
      exact ⟨(hWz e he w (hWb e he w hwe)).mpr hwe, hwim⟩
  have hNs : nonrealZeroCount s =
      ∑ e ∈ E, ∑ z ∈ (W e).filter (fun z => z.im ≠ 0), zeroMult (riemannHeat s) z := by
    rw [nonrealZeroCount_eq hs0, hF, Finset.filter_biUnion, Finset.sum_biUnion]
    intro e he e' he' hne
    exact Finset.disjoint_filter_filter (hWdisj he he' hne)
  -- the count in each disc
  have hdisc : ∀ e ∈ E, ∑ z ∈ (W e).filter (fun z => z.im ≠ 0), zeroMult (riemannHeat s) z =
      if e.im = 0 then zeroMult (riemannHeat t₁) e - zeroMult (riemannHeat t₁) e % 2
      else zeroMult (riemannHeat t₁) e := by
    intro e he
    split_ifs with him
    · have hδe : δ ≤ δr e :=
        ((min_le_left _ _).trans (min_le_right _ _)).trans
          (hδ₂le e (Finset.mem_filter.mpr ⟨he, him⟩))
      exact hδrprop e he him s (by linarith) hst (W e) (hWz e he) (hWb e he)
    · have hfil : (W e).filter (fun z => z.im ≠ 0) = W e :=
        Finset.filter_true_of_mem fun z hz => havoid e him z (hWb e he z hz)
      rw [hfil]
      have h1 := hWs e he
      rw [(hsm e he).1] at h1
      have h2 : ((∑ ρ ∈ W e, zeroMult (riemannHeat s) ρ : ℕ) : ℂ) =
          (zeroMult (riemannHeat t₁) e : ℂ) := by push_cast; exact h1.symm
      exact_mod_cast h2
  have hfnot : E.filter (fun e => ¬ e.im = 0) = Enr := by
    rw [hEnr]
  rw [hNs, Finset.sum_congr rfl hdisc, Finset.sum_ite, hfnot, hN₁, hcoll, add_comm]

/-! ## Collision times are isolated -/

/-- The nonreal count is constant just to the right of every `t₁ ∈ (0, 1/8)`. -/
theorem exists_right_nonrealZeroCount {t₁ : ℝ} (ht₁ : 0 < t₁) (ht₁8 : t₁ < 1 / 8) :
    ∃ δ > 0, ∀ s, t₁ < s → s < t₁ + δ → nonrealZeroCount s = nonrealZeroCount t₁ := by
  obtain ⟨δ, hδ, hlsc, hright⟩ := exists_local_nonrealZeroCount ht₁ ht₁8
  refine ⟨δ, hδ, fun s h1 h2 => le_antisymm (hright s h1 h2) (hlsc s ?_ (by linarith))⟩
  rw [abs_of_pos (by linarith)]
  linarith

/-- **Collision times are isolated.** Near every `u ∈ (0, 1/8]` the collision mass vanishes
except at `u`: on each side of `u` the count is constant, while a collision would make it jump. -/
theorem exists_collisionMass_eq_zero_near {u : ℝ} (hu : 0 < u) (hu8 : u ≤ 1 / 8) :
    ∃ δ > 0, ∀ s, |s - u| < δ → s ≠ u → collisionMass s = 0 := by
  obtain ⟨δL, hδL, hL⟩ := exists_left_nonrealZeroCount hu hu8
  obtain ⟨δR, hδR, hR⟩ : ∃ δR > 0, ∀ s, u < s → s < u + δR → s ≤ 1 / 8 →
      nonrealZeroCount s = nonrealZeroCount u := by
    rcases lt_or_eq_of_le hu8 with h | h
    · obtain ⟨δ, hδ, hr⟩ := exists_right_nonrealZeroCount hu h
      exact ⟨δ, hδ, fun s h1 h2 _ => hr s h1 h2⟩
    · exact ⟨1, one_pos, fun s h1 _ h3 => absurd h3 (by rw [← h]; exact not_le.mpr h1)⟩
  refine ⟨min (min δL δR) (u / 2), lt_min (lt_min hδL hδR) (by linarith), fun s hs hsu => ?_⟩
  have hs1 : |s - u| < δL := hs.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hs2 : |s - u| < δR := hs.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hs3 : |s - u| < u / 2 := hs.trans_le (min_le_right _ _)
  have hs0 : 0 < s := by rw [abs_lt] at hs3; linarith
  by_contra hJ
  have hs8 : s ≤ 1 / 8 := by
    by_contra h
    exact hJ (collisionMass_eq_zero_of_eighth_le (not_le.mp h).le)
  obtain ⟨δs, hδs, hLs⟩ := exists_left_nonrealZeroCount hs0 hs8
  rcases lt_or_gt_of_ne hsu with hlt | hgt
  · -- `s < u`: the count is constant on `(u − δL, u)`
    have hsL : u - δL < s := by rw [abs_lt] at hs1; linarith
    set s' := max (s - δs / 2) ((s + (u - δL)) / 2)
    have h1 : s - δs < s' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have h2 : s' < s := max_lt (by linarith) (by linarith)
    have h3 : u - δL < s' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have e1 := hLs s' h1 h2
    have e2 := hL s' h3 (h2.trans hlt)
    have e3 := hL s hsL hlt
    omega
  · -- `u < s`: the count is constant on `(u, u + δR)`
    have hsR : s < u + δR := by rw [abs_lt] at hs2; linarith
    set s' := max (s - δs / 2) ((s + u) / 2)
    have h1 : s - δs < s' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have h2 : s' < s := max_lt (by linarith) (by linarith)
    have h3 : u < s' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have e1 := hLs s' h1 h2
    have e2 := hR s' h3 (h2.trans hsR) (h2.le.trans hs8)
    have e3 := hR s hgt hsR hs8
    omega

/-- **Finitely many collisions after any positive time.** -/
theorem finite_collisionTimes {t : ℝ} (ht : 0 < t) :
    {s : ℝ | t < s ∧ collisionMass s ≠ 0}.Finite := by
  classical
  have hK : IsCompact (Icc t (1 / 8)) := isCompact_Icc
  have hloc : ∀ u ∈ Icc t (1 / 8), ∃ δ > 0, ∀ s, |s - u| < δ → s ≠ u → collisionMass s = 0 :=
    fun u hu => exists_collisionMass_eq_zero_near (ht.trans_le hu.1) hu.2
  choose! δ hδ hδprop using hloc
  obtain ⟨c, hcK, hcover⟩ := hK.elim_nhds_subcover (fun u => ball u (δ u))
    (fun u hu => ball_mem_nhds u (hδ u hu))
  refine c.finite_toSet.subset fun s hs => ?_
  obtain ⟨hts, hJ⟩ := hs
  have hs8 : s ≤ 1 / 8 := by
    by_contra h
    exact hJ (collisionMass_eq_zero_of_eighth_le (not_le.mp h).le)
  obtain ⟨u, hu, hsu⟩ := Set.mem_iUnion₂.mp (hcover ⟨hts.le, hs8⟩)
  rw [mem_ball, Real.dist_eq] at hsu
  by_contra hsc
  have hne : s ≠ u := by rintro rfl; exact hsc (Finset.mem_coe.mpr hu)
  exact hJ (hδprop u (hcK u hu) s hsu hne)

/-! ## The global collision law -/

/-- A function on `[a, b]` that is constant just to the right of each point of `[a, b)` and just
to the left of each point of `(a, b]` takes the same value at `b` as at `a`. -/
theorem eq_of_locally_const_Icc {F : ℝ → ℕ} {a b : ℝ} (hab : a ≤ b)
    (hright : ∀ u ∈ Ico a b, ∃ δ > 0, ∀ s, u < s → s < u + δ → F s = F u)
    (hleft : ∀ u ∈ Ioc a b, ∃ δ > 0, ∀ s, u - δ < s → s < u → F s = F u) : F b = F a := by
  set S := {u ∈ Icc a b | ∀ v ∈ Icc a u, F v = F a} with hS
  have haS : a ∈ S := ⟨⟨le_rfl, hab⟩, fun v hv => by rw [le_antisymm hv.2 hv.1]⟩
  have hbdd : BddAbove S := ⟨b, fun u hu => hu.1.2⟩
  set c := sSup S with hc
  have hac : a ≤ c := le_csSup hbdd haS
  have hcb : c ≤ b := csSup_le ⟨a, haS⟩ fun u hu => hu.1.2
  have hbelow : ∀ v ∈ Ico a c, F v = F a := by
    intro v hv
    obtain ⟨u, huS, hvu⟩ := exists_lt_of_lt_csSup ⟨a, haS⟩ hv.2
    exact huS.2 v ⟨hv.1, hvu.le⟩
  have hcS : c ∈ S := by
    refine ⟨⟨hac, hcb⟩, fun v hv => ?_⟩
    rcases lt_or_eq_of_le hv.2 with hlt | heq
    · exact hbelow v ⟨hv.1, hlt⟩
    · rw [heq]
      rcases lt_or_eq_of_le hac with hac' | hac'
      · obtain ⟨δ, hδ, hl⟩ := hleft c ⟨hac', hcb⟩
        set v' := max a (c - δ / 2)
        have h1 : c - δ < v' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
        have h2 : v' < c := max_lt hac' (by linarith)
        rw [← hl v' h1 h2]
        exact hbelow v' ⟨le_max_left _ _, h2⟩
      · rw [← hac']
  rcases lt_or_eq_of_le hcb with hlt | heq
  · exfalso
    obtain ⟨δ, hδ, hr⟩ := hright c ⟨hac, hlt⟩
    set c' := min b (c + δ / 2)
    have hcc' : c < c' := lt_min hlt (by linarith)
    have hc'S : c' ∈ S := by
      refine ⟨⟨by linarith, min_le_left _ _⟩, fun v hv => ?_⟩
      rcases le_or_gt v c with hvc | hvc
      · exact hcS.2 v ⟨hv.1, hvc⟩
      · have hv2 : v < c + δ :=
          lt_of_le_of_lt hv.2 (lt_of_le_of_lt (min_le_right _ _) (by linarith))
        rw [hr v hvc hv2]
        exact hcS.2 c ⟨hac, le_rfl⟩
    have := le_csSup hbdd hc'S
    linarith
  · rw [← heq]
    exact hcS.2 c ⟨hac, le_rfl⟩

/-- **The global collision law.** For `t > 0`, the nonreal count of `H_t` is the total collision
mass of the flow after `t`: `N(t) = Σ_{s > t} C(s)`, a finite sum over the collision times. The
function `u ↦ N(u) + Σ_{t < p ≤ u} C(p)` is locally constant on `[t, 1/8]`. -/
theorem nonrealZeroCount_eq_sum_collisionMass {t : ℝ} (ht : 0 < t) :
    nonrealZeroCount t = ∑ s ∈ (finite_collisionTimes ht).toFinset, collisionMass s := by
  classical
  set P := (finite_collisionTimes ht).toFinset with hP
  have hmemP : ∀ s, s ∈ P ↔ t < s ∧ collisionMass s ≠ 0 := fun s => by
    rw [hP, Set.Finite.mem_toFinset]; rfl
  have hP8 : ∀ p ∈ P, p ≤ 1 / 8 := fun p hp => by
    by_contra h
    exact ((hmemP p).mp hp).2 (collisionMass_eq_zero_of_eighth_le (not_le.mp h).le)
  rcases le_or_gt t (1 / 8) with ht8 | ht8
  swap
  · have hPe : P = ∅ := Finset.eq_empty_of_forall_notMem fun p hp => by
      have h1 := hP8 p hp
      have h2 := ((hmemP p).mp hp).1
      linarith
    rw [hPe, Finset.sum_empty, nonrealZeroCount_eq_zero_of_le ht8.le]
  set F : ℝ → ℕ := fun u => nonrealZeroCount u + ∑ p ∈ P.filter (· ≤ u), collisionMass p with hF
  have hFt : F t = nonrealZeroCount t := by
    simp only [hF]
    rw [Finset.filter_false_of_mem fun p hp => not_le.mpr ((hmemP p).mp hp).1, Finset.sum_empty,
      add_zero]
  have hF8 : F (1 / 8) = ∑ p ∈ P, collisionMass p := by
    simp only [hF]
    rw [Finset.filter_true_of_mem hP8, nonrealZeroCount_eq_zero_of_le le_rfl, zero_add]
  -- constancy to the right of each point of `[t, 1/8)`
  have hright : ∀ u ∈ Ico t (1 / 8), ∃ δ > 0, ∀ s, u < s → s < u + δ → F s = F u := by
    intro u hu
    obtain ⟨δ₁, hδ₁, hN⟩ := exists_right_nonrealZeroCount (ht.trans_le hu.1) hu.2
    obtain ⟨δ₂, hδ₂, hgap⟩ := exists_pos_le_finset_of_pos (P.filter (u < ·))
      (g := fun p => p - u) fun p hp => sub_pos.mpr (Finset.mem_filter.mp hp).2
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s h1 h2 => ?_⟩
    have hfil : P.filter (· ≤ s) = P.filter (· ≤ u) := by
      refine Finset.filter_congr fun p hp => ⟨fun hps => ?_, fun hpu => hpu.trans h1.le⟩
      by_contra hpu
      have h3 := hgap p (Finset.mem_filter.mpr ⟨hp, not_le.mp hpu⟩)
      have h4 := min_le_right δ₁ δ₂
      linarith
    simp only [hF]
    rw [hfil, hN s h1 (by linarith [min_le_left δ₁ δ₂])]
  -- constancy to the left of each point of `(t, 1/8]`
  have hleft : ∀ u ∈ Ioc t (1 / 8), ∃ δ > 0, ∀ s, u - δ < s → s < u → F s = F u := by
    intro u hu
    obtain ⟨δ₁, hδ₁, hN⟩ := exists_left_nonrealZeroCount (ht.trans hu.1) hu.2
    obtain ⟨δ₂, hδ₂, hgap⟩ := exists_pos_le_finset_of_pos (P.filter (· < u))
      (g := fun p => u - p) fun p hp => sub_pos.mpr (Finset.mem_filter.mp hp).2
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s h1 h2 => ?_⟩
    -- no collision time lies in `(s, u)`, so `Σ_{p ≤ u} = Σ_{p ≤ s} + C(u)`
    have hsplit : ∑ p ∈ P.filter (· ≤ u), collisionMass p =
        ∑ p ∈ P.filter (· ≤ s), collisionMass p + collisionMass u := by
      rw [← Finset.sum_filter_add_sum_filter_not (P.filter (· ≤ u)) (· ≤ s),
        Finset.filter_filter, Finset.filter_filter]
      congr 1
      · exact Finset.sum_congr (Finset.filter_congr fun p _ =>
          ⟨fun h => h.2, fun h => ⟨h.trans h2.le, h⟩⟩) fun _ _ => rfl
      · refine Finset.sum_eq_single u (fun b hb hbu => ?_) (fun hu' => ?_)
        · exfalso
          obtain ⟨hbP, hbu', hbs⟩ := Finset.mem_filter.mp hb
          have h3 := hgap b (Finset.mem_filter.mpr ⟨hbP, lt_of_le_of_ne hbu' hbu⟩)
          have h4 := min_le_right δ₁ δ₂
          linarith [not_le.mp hbs]
        · by_contra hJ
          exact hu' (Finset.mem_filter.mpr ⟨(hmemP u).mpr ⟨hu.1, hJ⟩, le_rfl, not_le.mpr h2⟩)
    simp only [hF]
    rw [hsplit, hN s (by linarith [min_le_left δ₁ δ₂]) h2]
    ring
  have h := eq_of_locally_const_Icc ht8 hright hleft
  rw [hF8, hFt] at h
  exact h.symm

/-- The total collision mass of the flow after time `t > 0` (`0` for `t ≤ 0`). -/
def collisionMassAfter (t : ℝ) : ℕ :=
  if ht : 0 < t then ∑ s ∈ (finite_collisionTimes ht).toFinset, collisionMass s else 0

theorem nonrealZeroCount_eq_collisionMassAfter {t : ℝ} (ht : 0 < t) :
    nonrealZeroCount t = collisionMassAfter t := by
  rw [collisionMassAfter, dif_pos ht, nonrealZeroCount_eq_sum_collisionMass ht]

/-- **RH is the absence of collisions.** RH holds iff no nonreal zero of the flow lands on the real
axis at any positive time. -/
theorem riemannHypothesis_iff_forall_collisionMass_eq_zero :
    RiemannHypothesis ↔ ∀ t, 0 < t → collisionMass t = 0 := by
  rw [riemannHypothesis_iff_eventually_nonrealZeroCount_eq_zero]
  constructor
  · intro h t ht
    -- the count vanishes at every positive time, so it never jumps
    have hzero : ∀ u, 0 < u → nonrealZeroCount u = 0 := by
      intro u hu
      obtain ⟨v, hv, hv0⟩ := (h.and (Ioo_mem_nhdsGT hu)).exists
      have := nonrealZeroCount_antitoneOn (mem_Ioi.mpr hv0.1) (mem_Ioi.mpr hu) hv0.2.le
      omega
    rcases le_or_gt t (1 / 8) with ht8 | ht8
    · obtain ⟨δ, hδ, hL⟩ := exists_left_nonrealZeroCount ht ht8
      have e := hL (t - min δ t / 2) (by linarith [min_le_left δ t, lt_min hδ ht])
        (by linarith [lt_min hδ ht])
      rw [hzero _ (by linarith [min_le_right δ t]), hzero t ht] at e
      omega
    · exact collisionMass_eq_zero_of_eighth_le ht8.le
  · intro h
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [nonrealZeroCount_eq_sum_collisionMass ht]
    exact Finset.sum_eq_zero fun s hs =>
      h s (ht.trans ((Set.Finite.mem_toFinset _).mp hs).1)

end

end RHTower.DeBruijn
