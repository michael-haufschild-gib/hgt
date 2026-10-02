import GaloisForLFunctions.RHTower.DeBruijnHeatForwardModel
import GaloisForLFunctions.RHTower.DeBruijnLaguerreEvolution
import GaloisForLFunctions.HTGeometry.HermiteSignChanges

/-!
# A real zero of order `k` of `H_s` leaves `k` distinct real zeros forward in time

Let `x₀` be a real zero of order `k` of `H_s` and `a = H_s^{(k)}(x₀)`, which is real and nonzero.  By
the forward local model, `H_{s+q²}(x₀ + qσ) = (a/k!) q^k Q_k(σ) + O(q^{k+1})` uniformly for bounded
`σ`, and `Q_k = √2^k Heₖ(·/√2)` changes sign across `k` points of the real axis that are separated
by more than the sign-change width (`exists_heatPoly_sign_changes`).  For small `q > 0` the real
function `y ↦ H_{s+q²}(y)` therefore changes sign across each of the `k` intervals
`x₀ + q(ρ − ε, ρ + ε)`, and the intermediate value theorem gives `k` distinct real zeros within
`qS` of `x₀` (`exists_real_zeros_forward`).
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

theorem heatModelFwd_ofReal (k : ℕ) (σ : ℝ) : heatModelFwd k σ = (heatPoly k σ : ℂ) := by
  simp only [heatModelFwd, heatPoly]
  push_cast
  rfl

/-- A positive lower bound for a positive function on a finite set. -/
theorem exists_pos_le_of_finset {Z : Finset ℝ} {g : ℝ → ℝ} (hg : ∀ ρ ∈ Z, 0 < g ρ) :
    ∃ m, 0 < m ∧ ∀ ρ ∈ Z, m ≤ g ρ := by
  rcases Z.eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun ρ hρ => by simp [he] at hρ⟩
  · exact ⟨Z.inf' hne g, (Finset.lt_inf'_iff hne).mpr hg, fun ρ hρ => Finset.inf'_le _ hρ⟩

/-- A continuous real function changing sign on `[u, v]` vanishes inside. -/
theorem exists_zero_of_mul_neg {f : ℝ → ℝ} (hf : Continuous f) {u v : ℝ} (huv : u < v)
    (h : f u * f v < 0) : ∃ c ∈ Ioo u v, f c = 0 := by
  rcases lt_or_gt_of_ne (show f u ≠ 0 by intro h0; rw [h0, zero_mul] at h; exact lt_irrefl _ h)
    with hu | hu
  · have hv : 0 < f v := by nlinarith
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo huv.le hf.continuousOn ⟨hu, hv⟩
    exact ⟨c, hc, hc0⟩
  · have hv : f v < 0 := by nlinarith
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo' huv.le hf.continuousOn ⟨hv, hu⟩
    exact ⟨c, hc, hc0⟩

/-- **Real zeros forward in time.** If the derivatives of `H_s` of order `< k` vanish at the real
point `x₀` and the `k`-th does not, then there are `S > 0` and `q₁ > 0` such that for
`0 < q ≤ q₁` the function `H_{s+q²}` has `k` distinct real zeros within `qS` of `x₀`. -/
theorem exists_real_zeros_forward {s : ℝ} (hs : 0 ≤ s) {x₀ : ℝ} {k : ℕ}
    (hvan : ∀ i < k, iteratedDeriv i (riemannHeat s) x₀ = 0)
    (ha : iteratedDeriv k (riemannHeat s) x₀ ≠ 0) :
    ∃ S, 0 < S ∧ ∃ q₁, 0 < q₁ ∧ ∀ q, 0 < q → q ≤ q₁ →
      ∃ Y : Finset ℝ, Y.card = k ∧ ∀ y ∈ Y, |y - x₀| < q * S ∧ riemannHeat (s + q ^ 2) y = 0 := by
  classical
  obtain ⟨Z, hZcard, ε, hε, hsign, hsep⟩ := exists_heatPoly_sign_changes k
  set S := ∑ ρ ∈ Z, |ρ| + ε + 1 with hS
  have hS0 : 0 < S := by have := Finset.sum_nonneg (fun ρ (_ : ρ ∈ Z) => abs_nonneg ρ); linarith
  have hρS : ∀ ρ ∈ Z, |ρ| + ε < S := by
    intro ρ hρ
    have := Finset.single_le_sum (fun ρ (_ : ρ ∈ Z) => abs_nonneg ρ) hρ
    linarith
  obtain ⟨C, q₀, hq₀, hmodel⟩ := exists_norm_riemannHeat_sub_heatModelFwd_le hs hvan hS0.le
  set a := iteratedDeriv k (riemannHeat s) x₀
  have haim : a.im = 0 := iteratedDeriv_riemannHeat_ofReal_im hs k x₀
  have hareal : a = (a.re : ℂ) := Complex.ext (by simp) (by simp [haim])
  have hare : a.re ≠ 0 := fun h => ha (Complex.ext h haim)
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_of_finset (Z := Z)
    (g := fun ρ => min |heatPoly k (ρ - ε)| |heatPoly k (ρ + ε)|) (fun ρ hρ => by
      have h := hsign ρ hρ
      have h1 : heatPoly k (ρ - ε) ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact lt_irrefl _ h
      have h2 : heatPoly k (ρ + ε) ≠ 0 := fun h0 => by rw [h0, mul_zero] at h; exact lt_irrefl _ h
      exact lt_min (abs_pos.mpr h1) (abs_pos.mpr h2))
  have hkf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  set A := |a.re| / k.factorial
  have hA : 0 < A := div_pos (abs_pos.mpr hare) hkf
  set q₁ := min q₀ (A * m / (|C| + 1))
  have hq₁ : 0 < q₁ := lt_min hq₀ (by positivity)
  refine ⟨S, hS0, q₁, hq₁, fun q hq hqq => ?_⟩
  have hqq₀ : q ≤ q₀ := hqq.trans (min_le_left _ _)
  have hqC : (|C| + 1) * q ≤ A * m := by
    have := hqq.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  set f : ℝ → ℝ := fun y => (riemannHeat (s + q ^ 2) y).re with hf
  have hfc : Continuous f :=
    Complex.continuous_re.comp ((differentiable_riemannHeat (by positivity)).continuous.comp
      Complex.continuous_ofReal)
  -- the sign of `f` at the model points
  have hpoint : ∀ σ : ℝ, |σ| ≤ S →
      0 < f (x₀ + q * σ) * (a.re / k.factorial * q ^ k * heatPoly k σ) ∨
        |heatPoly k σ| < m := by
    intro σ hσ
    by_cases hsm : |heatPoly k σ| < m
    · exact Or.inr hsm
    · left
      replace hsm := not_lt.mp hsm
      have hb := hmodel q hq.le hqq₀ σ (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hσ)
      set M : ℝ := a.re / k.factorial * q ^ k * heatPoly k σ with hM
      have hMc : iteratedDeriv k (riemannHeat s) x₀ / (k.factorial : ℂ) * (q : ℂ) ^ k *
          heatModelFwd k σ = (M : ℂ) := by
        rw [heatModelFwd_ofReal, hM]
        change a / _ * _ * _ = _
        conv_lhs => rw [hareal]
        push_cast
        ring
      have harg : (x₀ : ℂ) + (q : ℂ) * (σ : ℂ) = ((x₀ + q * σ : ℝ) : ℂ) := by push_cast; ring
      rw [hMc, harg] at hb
      have hre : |f (x₀ + q * σ) - M| ≤ C * q ^ (k + 1) := by
        have h1 := Complex.abs_re_le_norm (riemannHeat (s + q ^ 2) ((x₀ + q * σ : ℝ) : ℂ) - (M : ℂ))
        rw [Complex.sub_re, Complex.ofReal_re] at h1
        exact h1.trans hb
      have hMabs : A * m * q ^ k ≤ |M| := by
        rw [hM, abs_mul, abs_mul, abs_div, Nat.abs_cast, abs_of_pos (pow_pos hq k)]
        have : A * m * q ^ k = |a.re| / k.factorial * q ^ k * m := by simp only [A]; ring
        rw [this]
        gcongr
      have hCq : C * q ^ (k + 1) < A * m * q ^ k := by
        have hqk : 0 < q ^ k := pow_pos hq k
        have e : C * q ^ (k + 1) = (C * q) * q ^ k := by ring
        rw [e]
        have hCq' : C * q < A * m := by
          have : C * q ≤ |C| * q := by gcongr; exact le_abs_self C
          nlinarith
        exact mul_lt_mul_of_pos_right hCq' hqk
      have hlt : |f (x₀ + q * σ) - M| < |M| := by linarith
      rcases lt_or_gt_of_ne (show M ≠ 0 by
          intro h0; rw [h0, abs_zero] at hlt; exact (not_lt.mpr (abs_nonneg _)) hlt) with hneg | hpos
      · rw [abs_of_neg hneg] at hlt
        have := (abs_lt.mp hlt).2
        nlinarith
      · rw [abs_of_pos hpos] at hlt
        have := (abs_lt.mp hlt).1
        nlinarith
  -- a zero in each sign-change interval
  have hzero : ∀ ρ ∈ Z, ∃ c, c ∈ Ioo (x₀ + q * (ρ - ε)) (x₀ + q * (ρ + ε)) ∧ f c = 0 := by
    intro ρ hρ
    have hσ1 : |ρ - ε| ≤ S := by
      have := abs_sub (ρ) ε; rw [abs_of_pos hε] at this; linarith [hρS ρ hρ]
    have hσ2 : |ρ + ε| ≤ S := by
      have := abs_add_le ρ ε; rw [abs_of_pos hε] at this; linarith [hρS ρ hρ]
    have hm1 : m ≤ |heatPoly k (ρ - ε)| := (hmle ρ hρ).trans (min_le_left _ _)
    have hm2 : m ≤ |heatPoly k (ρ + ε)| := (hmle ρ hρ).trans (min_le_right _ _)
    have h1 := (hpoint (ρ - ε) hσ1).resolve_right (not_lt.mpr hm1)
    have h2 := (hpoint (ρ + ε) hσ2).resolve_right (not_lt.mpr hm2)
    have hQ := hsign ρ hρ
    have hc0 : 0 < (a.re / k.factorial * q ^ k) ^ 2 := by
      have : a.re / k.factorial * q ^ k ≠ 0 :=
        mul_ne_zero (div_ne_zero hare hkf.ne') (pow_ne_zero _ hq.ne')
      positivity
    have hneg : f (x₀ + q * (ρ - ε)) * f (x₀ + q * (ρ + ε)) < 0 := by
      have hprod := mul_pos h1 h2
      have e : f (x₀ + q * (ρ - ε)) * (a.re / k.factorial * q ^ k * heatPoly k (ρ - ε)) *
          (f (x₀ + q * (ρ + ε)) * (a.re / k.factorial * q ^ k * heatPoly k (ρ + ε))) =
          (f (x₀ + q * (ρ - ε)) * f (x₀ + q * (ρ + ε))) *
            ((a.re / k.factorial * q ^ k) ^ 2 * (heatPoly k (ρ - ε) * heatPoly k (ρ + ε))) := by
        ring
      rw [e] at hprod
      have hneg2 : (a.re / k.factorial * q ^ k) ^ 2 * (heatPoly k (ρ - ε) * heatPoly k (ρ + ε)) < 0 :=
        mul_neg_of_pos_of_neg hc0 hQ
      nlinarith
    have hlt : x₀ + q * (ρ - ε) < x₀ + q * (ρ + ε) := by nlinarith
    obtain ⟨c, hc, hc0⟩ := exists_zero_of_mul_neg hfc hlt hneg
    exact ⟨c, hc, hc0⟩
  choose! c hcI hc0 using hzero
  refine ⟨Z.image c, ?_, fun y hy => ?_⟩
  · rw [Finset.card_image_of_injOn, hZcard]
    intro ρ hρ ρ' hρ' heq
    by_contra hne
    have h1 := hcI ρ hρ
    have h2 := hcI ρ' hρ'
    have hs' := hsep ρ hρ ρ' hρ' hne
    rw [heq] at h1
    have hd : q * |ρ - ρ'| < q * (2 * ε) := by
      rcases le_or_gt ρ ρ' with hle | hgt
      · rw [abs_of_nonpos (by linarith)]
        nlinarith [h1.1, h1.2, h2.1, h2.2]
      · rw [abs_of_pos (by linarith)]
        nlinarith [h1.1, h1.2, h2.1, h2.2]
    have : |ρ - ρ'| < 2 * ε := lt_of_mul_lt_mul_left hd hq.le
    linarith
  · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hy
    have hI := hcI ρ hρ
    refine ⟨?_, ?_⟩
    · have hρ' := hρS ρ hρ
      rw [abs_lt]
      constructor
      · have : -|ρ| ≤ ρ := neg_abs_le ρ
        nlinarith [hI.1]
      · have : ρ ≤ |ρ| := le_abs_self ρ
        nlinarith [hI.2]
    · have hre := hc0 ρ hρ
      have him := riemannHeat_ofReal_im (show 0 ≤ s + q ^ 2 by positivity) (c ρ)
      exact Complex.ext hre him

end

end RHTower.DeBruijn
