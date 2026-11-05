import GaloisForLFunctions.RHTower.DeBruijnCollisionJumpLaw
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatTimeSpreadsTheConfiguration

/-!
# Collisions blow up to Hermite profiles

At a zero of order `k` of `H_{s₀}`, with `a = H_{s₀}^{(k)}(z₀)`, the parabolic rescaling converges:

`H_{s₀+q²}(z₀ + qσ)/q^k → (a/k!) Q_k(σ)`,   `H_{s₀−q²}(z₀ + qσ)/q^k → (a/k!) P_k(σ)`,

uniformly on compact sets of `σ` (`blowup_forward`, `blowup_backward`). `Q_k = e^{−D²}σ^k` has `k` simple real
roots, and `P_k = e^{D²}σ^k` has `k − k mod 2` roots off the real axis. So each collision is a Hermite profile
of its order, whatever the source.

* **The zeros follow the roots** (`exists_zero_near_root_forward`). Just above a real zero of order `k`,
  each root `ρ` of `Q_k` carries a real zero of `H_{s₀+q²}` within `εq` of `x₀ + qρ`.
* **Order two** (`order_two_gap_law`). `Q₂ = σ² − 2`, so a simple collision opens at `g² ∼ 8(t − t₀)`.
* **Hermite gaps** (`exists_close_zeros_forward`). `kΣρ² − (Σρ)² = 2k²(k−1)` for the roots of `Q_k`, while a set of
  `k` reals with least gap `μ` has at least `μ² k²(k²−1)/12` here. So the least gap of `Q_k` satisfies
  `μ² ≤ 24/(k+1)`, and an order-`k` zero is followed by two real zeros with `g² ≤ (24/(k+1) + ε)(t − t₀)`.
-/

open Complex Filter Topology Set Metric Polynomial
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ZeroConfigurationGeometry
open RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-! ## The blow-up limits -/

/-- **Forward blow-up.** Above a zero of order `≥ k`, the rescaled flow converges to `(a/k!) Q_k`. -/
theorem blowup_forward {s : ℝ} (hs : 0 ≤ s) {z₀ : ℂ} {k : ℕ}
    (hvan : ∀ i < k, iteratedDeriv i (riemannHeat s) z₀ = 0) {S ε : ℝ} (hS : 0 ≤ S) (hε : 0 < ε) :
    ∃ q₁ > 0, ∀ q : ℝ, 0 < q → q ≤ q₁ → ∀ σ : ℂ, ‖σ‖ ≤ S →
      ‖riemannHeat (s + q ^ 2) (z₀ + q * σ) / (q : ℂ) ^ k -
        iteratedDeriv k (riemannHeat s) z₀ / (k.factorial : ℂ) * heatModelFwd k σ‖ ≤ ε := by
  obtain ⟨C, q₀, hq₀, hmodel⟩ := exists_norm_riemannHeat_sub_heatModelFwd_le hs hvan hS
  refine ⟨min q₀ (ε / (|C| + 1)), lt_min hq₀ (by positivity), fun q hq hq₁ σ hσ => ?_⟩
  have hb := hmodel q hq.le (hq₁.trans (min_le_left _ _)) σ hσ
  have hqk : (0 : ℝ) < q ^ k := pow_pos hq k
  have hne : (q : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.ne')
  have heq : riemannHeat (s + q ^ 2) (z₀ + q * σ) / (q : ℂ) ^ k -
      iteratedDeriv k (riemannHeat s) z₀ / (k.factorial : ℂ) * heatModelFwd k σ =
      (riemannHeat (s + q ^ 2) (z₀ + q * σ) -
        iteratedDeriv k (riemannHeat s) z₀ / (k.factorial : ℂ) * (q : ℂ) ^ k * heatModelFwd k σ) /
        (q : ℂ) ^ k := by
    field_simp
  rw [heq, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq,
    div_le_iff₀ hqk]
  have hqle : q * (|C| + 1) ≤ ε := by
    have := hq₁.trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity)] at this
  calc _ ≤ C * q ^ (k + 1) := hb
    _ ≤ (|C| + 1) * q ^ (k + 1) := by
      gcongr
      linarith only [le_abs_self C]
    _ = (q * (|C| + 1)) * q ^ k := by rw [pow_succ]; ring
    _ ≤ ε * q ^ k := by gcongr

/-- **Backward blow-up.** Below a zero of order `≥ k`, the rescaled flow converges to `(a/k!) P_k`. -/
theorem blowup_backward {s : ℝ} (hs : 0 ≤ s) {z₀ : ℂ} {k : ℕ}
    (hvan : ∀ i < k, iteratedDeriv i (riemannHeat s) z₀ = 0) {S ε : ℝ} (hS : 0 ≤ S) (hε : 0 < ε) :
    ∃ q₁ > 0, ∀ q : ℝ, 0 < q → q ≤ q₁ → q ^ 2 ≤ s → ∀ σ : ℂ, ‖σ‖ ≤ S →
      ‖riemannHeat (s - q ^ 2) (z₀ + q * σ) / (q : ℂ) ^ k -
        iteratedDeriv k (riemannHeat s) z₀ / (k.factorial : ℂ) * heatModel k σ‖ ≤ ε := by
  obtain ⟨C, q₀, hq₀, hmodel⟩ := exists_norm_riemannHeat_sub_heatModel_le hs hvan hS
  refine ⟨min q₀ (ε / (|C| + 1)), lt_min hq₀ (by positivity), fun q hq hq₁ hqs σ hσ => ?_⟩
  have hb := hmodel q hq.le (hq₁.trans (min_le_left _ _)) hqs σ hσ
  have hqk : (0 : ℝ) < q ^ k := pow_pos hq k
  have hne : (q : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.ne')
  have heq : riemannHeat (s - q ^ 2) (z₀ + q * σ) / (q : ℂ) ^ k -
      iteratedDeriv k (riemannHeat s) z₀ / (k.factorial : ℂ) * heatModel k σ =
      (riemannHeat (s - q ^ 2) (z₀ + q * σ) -
        iteratedDeriv k (riemannHeat s) z₀ / (k.factorial : ℂ) * (q : ℂ) ^ k * heatModel k σ) /
        (q : ℂ) ^ k := by
    field_simp
  rw [heq, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq,
    div_le_iff₀ hqk]
  have hqle : q * (|C| + 1) ≤ ε := by
    have := hq₁.trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity)] at this
  calc _ ≤ C * q ^ (k + 1) := hb
    _ ≤ (|C| + 1) * q ^ (k + 1) := by
      gcongr
      linarith only [le_abs_self C]
    _ = (q * (|C| + 1)) * q ^ k := by rw [pow_succ]; ring
    _ ≤ ε * q ^ k := by gcongr

/-! ## The roots of the profile -/

/-- The roots of the forward profile `Q_k`. -/
def profileRoots (k : ℕ) : Finset ℝ :=
  (realHermite k).roots.toFinset.image (fun y => Real.sqrt 2 * y)

theorem card_profileRoots (k : ℕ) : (profileRoots k).card = k := by
  classical
  obtain ⟨hnd, hcard⟩ := realHermite_roots_nodup_card k
  have hinj : Function.Injective (fun y : ℝ => Real.sqrt 2 * y) :=
    fun a b h => mul_left_cancel₀ (by positivity : Real.sqrt 2 ≠ 0) h
  rw [profileRoots, Finset.card_image_of_injective _ hinj, Multiset.toFinset_card_of_nodup hnd, hcard]

theorem heatPoly_eq_zero_of_mem {k : ℕ} {ρ : ℝ} (hρ : ρ ∈ profileRoots k) : heatPoly k ρ = 0 := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hρ
  have hroot : (realHermite k).IsRoot y := (mem_roots (realHermite_ne_zero k)).mp
    (Multiset.mem_toFinset.mp hy)
  rw [eval_heatPoly_eq, mul_div_cancel_left₀ _ (by positivity : Real.sqrt 2 ≠ 0), hroot.eq_zero,
    mul_zero]

/-- Each root of `Q_k` is a sign change at every small radius. -/
theorem exists_sign_change_at_root {k : ℕ} {ρ : ℝ} (hρ : ρ ∈ profileRoots k) :
    ∃ η > 0, ∀ ε, 0 < ε → ε < η → heatPoly k (ρ - ε) * heatPoly k (ρ + ε) < 0 := by
  classical
  obtain ⟨hnd, -⟩ := realHermite_roots_nodup_card k
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hρ
  have hroot : (realHermite k).IsRoot y := (mem_roots (realHermite_ne_zero k)).mp
    (Multiset.mem_toFinset.mp hy)
  obtain ⟨η, hη, hsign⟩ := exists_sign_change_of_derivative_ne_zero hroot
    (derivative_eval_ne_zero_of_roots_nodup (realHermite_ne_zero k) hnd hroot)
  have hs : 0 < Real.sqrt 2 := by positivity
  refine ⟨Real.sqrt 2 * η, by positivity, fun ε hε hεη => ?_⟩
  have hε' : 0 < ε / Real.sqrt 2 := by positivity
  have hεη' : ε / Real.sqrt 2 < η := by
    rw [div_lt_iff₀ hs]
    linarith only [hεη, mul_comm (Real.sqrt 2) η]
  have h := hsign _ hε' hεη'
  rw [eval_heatPoly_eq, eval_heatPoly_eq]
  have e1 : (Real.sqrt 2 * y - ε) / Real.sqrt 2 = y - ε / Real.sqrt 2 := by field_simp
  have e2 : (Real.sqrt 2 * y + ε) / Real.sqrt 2 = y + ε / Real.sqrt 2 := by field_simp
  rw [e1, e2]
  have hp : 0 < Real.sqrt 2 ^ k * Real.sqrt 2 ^ k := by positivity
  nlinarith only [mul_neg_of_pos_of_neg hp h]

theorem heatModelFwd_ofReal' (k : ℕ) (σ : ℝ) : heatModelFwd k σ = (heatPoly k σ : ℂ) :=
  heatModelFwd_ofReal k σ

/-- **Zeros follow the roots.** Above a real zero of exact order `k`, every root `ρ` of `Q_k` carries a real zero
of `H_{s+q²}` within `εq` of `x₀ + qρ`. -/
theorem exists_zero_near_root_forward {s : ℝ} (hs : 0 ≤ s) {x₀ : ℝ} {k : ℕ}
    (hvan : ∀ i < k, iteratedDeriv i (riemannHeat s) x₀ = 0)
    (ha : iteratedDeriv k (riemannHeat s) x₀ ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₁ > 0, ∀ q, 0 < q → q ≤ q₁ → ∀ ρ ∈ profileRoots k,
      ∃ y : ℝ, |y - (x₀ + q * ρ)| ≤ ε * q ∧ riemannHeat (s + q ^ 2) (y : ℂ) = 0 := by
  classical
  set a := iteratedDeriv k (riemannHeat s) x₀ with ha'
  have haim : a.im = 0 := iteratedDeriv_riemannHeat_ofReal_im hs k x₀
  have hare : a.re ≠ 0 := fun h => ha (Complex.ext h haim)
  have hAlt (ρ : ℝ) (hρ : ρ ∈ profileRoots k) : ∃ ε' > 0, ε' ≤ ε ∧
      heatPoly k (ρ - ε') * heatPoly k (ρ + ε') < 0 := by
    obtain ⟨η, hη, hsign⟩ := exists_sign_change_at_root hρ
    refine ⟨min ε (η / 2), lt_min hε (by positivity), min_le_left _ _, hsign _ (lt_min hε (by positivity)) ?_⟩
    linarith only [min_le_right ε (η / 2), hη]
  choose! ε' hε'pos hε'le hε'sign using hAlt
  -- a uniform scale for the sign tests
  set A : ℝ := |a.re| / (k.factorial : ℝ) with hA
  have hApos : 0 < A := by rw [hA]; positivity
  have hgap (ρ : ℝ) (hρ : ρ ∈ profileRoots k) :
      0 < min |heatPoly k (ρ - ε' ρ)| |heatPoly k (ρ + ε' ρ)| := by
    have h := hε'sign ρ hρ
    refine lt_min (abs_pos.mpr fun h0 => ?_) (abs_pos.mpr fun h0 => ?_)
    · rw [h0, zero_mul] at h; exact lt_irrefl _ h
    · rw [h0, mul_zero] at h; exact lt_irrefl _ h
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_finset_of_pos (profileRoots k) hgap
  set S := ∑ ρ ∈ profileRoots k, (|ρ| + ε' ρ) + 1 with hS
  have hSn : 0 ≤ S := by
    have := Finset.sum_nonneg (s := profileRoots k) (f := fun ρ => |ρ| + ε' ρ)
      (fun ρ hρ => add_nonneg (abs_nonneg ρ) (hε'pos ρ hρ).le)
    linarith only [this]
  have hSρ (ρ : ℝ) (hρ : ρ ∈ profileRoots k) : |ρ| + ε' ρ ≤ S := by
    have := Finset.single_le_sum (s := profileRoots k) (f := fun ρ => |ρ| + ε' ρ)
      (fun ρ hρ => add_nonneg (abs_nonneg ρ) (hε'pos ρ hρ).le) hρ
    linarith only [this]
  obtain ⟨q₁, hq₁, hblow⟩ := blowup_forward hs hvan hSn (ε := A * m / 2) (by positivity)
  refine ⟨q₁, hq₁, fun q hq hqq ρ hρ => ?_⟩
  set e := ε' ρ
  have he := hε'pos ρ hρ
  -- the real function along the blow-up
  set f : ℝ → ℝ := fun σ => (riemannHeat (s + q ^ 2) ((x₀ + q * σ : ℝ) : ℂ)).re with hf
  have hs' : 0 ≤ s + q ^ 2 := by positivity
  have hreal (σ : ℝ) : riemannHeat (s + q ^ 2) ((x₀ + q * σ : ℝ) : ℂ) = (f σ : ℂ) := by
    have him := iteratedDeriv_riemannHeat_ofReal_im hs' 0 (x₀ + q * σ)
    rw [iteratedDeriv_zero] at him
    exact Complex.ext (by simp [hf]) (by simpa using him)
  have hfc : Continuous f := by
    have := (differentiable_riemannHeat hs').continuous
    simp only [hf]
    fun_prop
  -- comparison with the profile at the two test points
  have htest (σ : ℝ) (hσ : |σ| ≤ S) :
      |f σ / q ^ k - a.re / (k.factorial : ℝ) * heatPoly k σ| ≤ A * m / 2 := by
    have h := hblow q hq hqq (σ : ℂ) (by rwa [Complex.norm_real, Real.norm_eq_abs])
    have e0 : (x₀ : ℂ) + q * σ = ((x₀ + q * σ : ℝ) : ℂ) := by push_cast; ring
    rw [e0, hreal σ, heatModelFwd_ofReal] at h
    have hareal : a = (a.re : ℂ) := Complex.ext (by simp) (by simp [haim])
    have e1 : (f σ : ℂ) / (q : ℂ) ^ k - a / (k.factorial : ℂ) * (heatPoly k σ : ℂ) =
        ((f σ / q ^ k - a.re / (k.factorial : ℝ) * heatPoly k σ : ℝ) : ℂ) := by
      rw [hareal]
      push_cast
      simp
    rw [e1, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have hρ1 : |ρ - e| ≤ S := by
    have := hSρ ρ hρ
    have h1 := abs_sub ρ e
    rw [abs_of_pos he] at h1
    linarith only [this, h1]
  have hρ2 : |ρ + e| ≤ S := by
    have := hSρ ρ hρ
    have h1 := abs_add_le ρ e
    rw [abs_of_pos he] at h1
    linarith only [this, h1]
  have h1 := htest _ hρ1
  have h2 := htest _ hρ2
  have hm1 : m ≤ |heatPoly k (ρ - e)| := (hmle ρ hρ).trans (min_le_left _ _)
  have hm2 : m ≤ |heatPoly k (ρ + e)| := (hmle ρ hρ).trans (min_le_right _ _)
  have hsign := hε'sign ρ hρ
  -- the sign of `f` agrees with that of `a Q_k`
  have hprod : f (ρ - e) * f (ρ + e) < 0 := by
    set B := a.re / (k.factorial : ℝ) with hB
    have hBA : |B| = A := by
      rw [hB, hA, abs_div, abs_of_pos (by positivity : (0 : ℝ) < k.factorial)]
    have hqk : (0 : ℝ) < q ^ k := pow_pos hq k
    set u := f (ρ - e) / q ^ k with hu
    set v := f (ρ + e) / q ^ k with hv
    have huv : f (ρ - e) * f (ρ + e) = (u * v) * (q ^ k * q ^ k) := by
      rw [hu, hv]
      field_simp
    rw [huv]
    refine mul_neg_of_neg_of_pos ?_ (by positivity)
    -- `u` has the sign of `B Q(ρ−e)` and `v` that of `B Q(ρ+e)`
    have hBQ1 : A * m ≤ |B * heatPoly k (ρ - e)| := by
      rw [abs_mul, hBA]
      exact mul_le_mul_of_nonneg_left hm1 hApos.le
    have hBQ2 : A * m ≤ |B * heatPoly k (ρ + e)| := by
      rw [abs_mul, hBA]
      exact mul_le_mul_of_nonneg_left hm2 hApos.le
    have hBB : (B * heatPoly k (ρ - e)) * (B * heatPoly k (ρ + e)) < 0 := by
      have hB2 : 0 < B * B := by
        have : B ≠ 0 := by
          intro h0
          rw [h0, abs_zero] at hBA
          exact hApos.ne hBA
        exact mul_self_pos.mpr this
      nlinarith only [mul_neg_of_pos_of_neg hB2 hsign]
    have hAm : 0 < A * m := by positivity
    rcases abs_le.mp h1 with ⟨h1a, h1b⟩
    rcases abs_le.mp h2 with ⟨h2a, h2b⟩
    rcases lt_or_ge (B * heatPoly k (ρ - e)) 0 with hneg | hnn
    · have hq2 : 0 < B * heatPoly k (ρ + e) := by
        by_contra hc
        have := mul_nonneg_of_nonpos_of_nonpos hneg.le (not_lt.mp hc)
        linarith only [this, hBB]
      rw [abs_of_neg hneg] at hBQ1
      rw [abs_of_pos hq2] at hBQ2
      have hu0 : u < 0 := by linarith only [h1b, hBQ1, hAm]
      have hv0 : 0 < v := by linarith only [h2a, hBQ2, hAm]
      exact mul_neg_of_neg_of_pos hu0 hv0
    · have hq2 : B * heatPoly k (ρ + e) < 0 := by
        by_contra hc
        have := mul_nonneg hnn (not_lt.mp hc)
        linarith only [this, hBB]
      rw [abs_of_nonneg hnn] at hBQ1
      rw [abs_of_neg hq2] at hBQ2
      have hu0 : 0 < u := by linarith only [h1a, hBQ1, hAm]
      have hv0 : v < 0 := by linarith only [h2b, hBQ2, hAm]
      exact mul_neg_of_pos_of_neg hu0 hv0
  obtain ⟨c, hc, hc0⟩ := exists_zero_of_mul_neg hfc (by linarith only [he] : ρ - e < ρ + e) hprod
  refine ⟨x₀ + q * c, ?_, ?_⟩
  · have hce : |c - ρ| ≤ ε' ρ := abs_le.mpr ⟨by linarith only [hc.1], by linarith only [hc.2]⟩
    have hrw : x₀ + q * c - (x₀ + q * ρ) = q * (c - ρ) := by ring
    rw [hrw, abs_mul, abs_of_pos hq]
    calc q * |c - ρ| ≤ q * ε := by
          gcongr
          exact hce.trans (hε'le ρ hρ)
      _ = ε * q := mul_comm _ _
  · rw [hreal c, hc0]
    simp

/-! ## Order two -/

theorem heatPoly_two (x : ℝ) : heatPoly 2 x = x ^ 2 - 2 := by
  simp [heatPoly, Finset.sum_range_succ, Nat.factorial]
  ring

/-- `Q₂` has the roots `±√2`. -/
theorem profileRoots_two : profileRoots 2 = {Real.sqrt 2, -Real.sqrt 2} := by
  classical
  have hs : 0 < Real.sqrt 2 := by positivity
  have hsub : profileRoots 2 ⊆ {Real.sqrt 2, -Real.sqrt 2} := by
    intro ρ hρ
    have h := heatPoly_eq_zero_of_mem hρ
    rw [heatPoly_two] at h
    have h2 : (ρ - Real.sqrt 2) * (ρ + Real.sqrt 2) = 0 := by
      have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith only [h, this]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact Finset.mem_insert.mpr (Or.inl (by linarith only [h3]))
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (by linarith only [h3]))
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [card_profileRoots]
  exact Finset.card_le_two

/-- **The gap law at a simple collision.** Just above a real zero of exact order two the flow has two real
zeros at `x₀ ± √2 q(1 + O(ε))`, so that `g² = 8q²(1 + O(ε))`, where `q² = t − t₀`. -/
theorem order_two_gap_law {s : ℝ} (hs : 0 ≤ s) {x₀ : ℝ}
    (h0 : riemannHeat s (x₀ : ℂ) = 0) (h1 : deriv (riemannHeat s) (x₀ : ℂ) = 0)
    (h2 : iteratedDeriv 2 (riemannHeat s) (x₀ : ℂ) ≠ 0) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ q₁ > 0, ∀ q, 0 < q → q ≤ q₁ → ∃ ym yp : ℝ, ym < yp ∧
      riemannHeat (s + q ^ 2) (ym : ℂ) = 0 ∧ riemannHeat (s + q ^ 2) (yp : ℂ) = 0 ∧
      |yp - (x₀ + q * Real.sqrt 2)| ≤ ε * q ∧ |ym - (x₀ - q * Real.sqrt 2)| ≤ ε * q ∧
      |(yp - ym) ^ 2 - 8 * q ^ 2| ≤ 14 * ε * q ^ 2 := by
  have hvan : ∀ i < 2, iteratedDeriv i (riemannHeat s) (x₀ : ℂ) = 0 := by
    intro i hi
    interval_cases i
    · simpa using h0
    · simpa [iteratedDeriv_one] using h1
  obtain ⟨q₁, hq₁, hnear⟩ := exists_zero_near_root_forward hs hvan h2 hε
  refine ⟨q₁, hq₁, fun q hq hqq => ?_⟩
  have hs2 : (1 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt 2 < 3 / 2 := by
    nlinarith only [hsq, hs2]
  obtain ⟨yp, hyp, hzp⟩ := hnear q hq hqq (Real.sqrt 2) (by rw [profileRoots_two]; simp)
  obtain ⟨ym, hym, hzm⟩ := hnear q hq hqq (-Real.sqrt 2) (by rw [profileRoots_two]; simp)
  rw [show x₀ + q * -Real.sqrt 2 = x₀ - q * Real.sqrt 2 by ring] at hym
  obtain ⟨hp1, hp2⟩ := abs_le.mp hyp
  obtain ⟨hm1, hm2⟩ := abs_le.mp hym
  have hgap1 : (2 * Real.sqrt 2 - 2 * ε) * q ≤ yp - ym := by nlinarith only [hp1, hm2]
  have hgap2 : yp - ym ≤ (2 * Real.sqrt 2 + 2 * ε) * q := by nlinarith only [hp2, hm1]
  have hpos : 0 < (2 * Real.sqrt 2 - 2 * ε) * q := by
    apply mul_pos _ hq
    linarith only [hs2, hε2]
  refine ⟨ym, yp, by linarith only [hgap1, hpos], hzm, hzp, hyp, hym, ?_⟩
  have hup : (yp - ym) ^ 2 ≤ ((2 * Real.sqrt 2 + 2 * ε) * q) ^ 2 :=
    pow_le_pow_left₀ (by linarith only [hgap1, hpos]) hgap2 2
  have hlo : ((2 * Real.sqrt 2 - 2 * ε) * q) ^ 2 ≤ (yp - ym) ^ 2 :=
    pow_le_pow_left₀ hpos.le hgap1 2
  have hq2 : 0 < q ^ 2 := by positivity
  have hup' : ((2 * Real.sqrt 2 + 2 * ε) * q) ^ 2 ≤ (8 + 14 * ε) * q ^ 2 := by
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_right _ hq2.le
    nlinarith only [hsq, hs3, hε, hε2]
  have hlo' : (8 - 14 * ε) * q ^ 2 ≤ ((2 * Real.sqrt 2 - 2 * ε) * q) ^ 2 := by
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_right _ hq2.le
    nlinarith only [hsq, hs3, hε, sq_nonneg ε]
  refine abs_le.mpr ⟨by linarith only [hlo, hlo'], by linarith only [hup, hup']⟩

/-! ## Packing: a separated set has a large spread -/

/-- Distances from a point to a separated set lying below it dominate the arithmetic progression. -/
theorem sum_sq_ge_of_sep {μ : ℝ} (hμ : 0 ≤ μ) (s : Finset ℝ) :
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → μ ≤ |x - y|) → ∀ a c : ℝ, 0 ≤ c → (∀ x ∈ s, μ ≤ a - x) →
      ∑ m ∈ Finset.range s.card, (((m : ℝ) + 1) * μ + c) ^ 2 ≤ ∑ x ∈ s, (a - x + c) ^ 2 := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert b s hb ih =>
    intro hsep a c hc hle
    have hbs : b ∉ s := fun h => lt_irrefl _ (hb b h)
    have hsep' : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → μ ≤ |x - y| := fun x hx y hy hxy =>
      hsep x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    have hbx (x : ℝ) (hx : x ∈ s) : μ ≤ b - x := by
      have h1 := hsep b (Finset.mem_insert_self _ _) x (Finset.mem_insert_of_mem hx) (hb x hx).ne'
      rwa [abs_of_pos (by linarith only [hb x hx])] at h1
    have hab : μ ≤ a - b := hle b (Finset.mem_insert_self _ _)
    have hih := ih hsep' b (μ + c) (by linarith only [hμ, hc]) hbx
    rw [Finset.card_insert_of_notMem hbs, Finset.sum_range_succ', Finset.sum_insert hbs]
    have hhead : (((0 : ℕ) : ℝ) + 1) * μ + c ≤ a - b + c := by
      push_cast
      linarith only [hab]
    have hheads := pow_le_pow_left₀ (by push_cast; linarith only [hμ, hc]) hhead 2
    have hrest : ∑ x ∈ s, (b - x + (μ + c)) ^ 2 ≤ ∑ x ∈ s, (a - x + c) ^ 2 := by
      refine Finset.sum_le_sum fun x hx => pow_le_pow_left₀ ?_ ?_ 2
      · linarith only [hbx x hx, hμ, hc]
      · linarith only [hab]
    have hterm : ∑ m ∈ Finset.range s.card, ((((m + 1 : ℕ) : ℝ) + 1) * μ + c) ^ 2 =
        ∑ m ∈ Finset.range s.card, (((m : ℝ) + 1) * μ + (μ + c)) ^ 2 := by
      refine Finset.sum_congr rfl fun m _ => ?_
      push_cast
      ring
    rw [hterm]
    linarith only [hih, hrest, hheads]

theorem sum_range_add_one_sq (n : ℕ) :
    ∑ m ∈ Finset.range n, ((m : ℝ) + 1) ^ 2 = (n : ℝ) * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- A set of `n` reals with least gap `μ` has `nΣx² − (Σx)² ≥ μ² n²(n²−1)/12`. -/
theorem spread_ge_of_sep {μ : ℝ} (hμ : 0 ≤ μ) (s : Finset ℝ) :
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → μ ≤ |x - y|) →
      μ ^ 2 * ((s.card : ℝ) ^ 2 * ((s.card : ℝ) ^ 2 - 1) / 12) ≤
        (s.card : ℝ) * ∑ x ∈ s, x ^ 2 - (∑ x ∈ s, x) ^ 2 := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert b s hb ih =>
    intro hsep
    have hbs : b ∉ s := fun h => lt_irrefl _ (hb b h)
    have hih := ih fun x hx y hy hxy =>
      hsep x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    have hdist := sum_sq_ge_of_sep hμ s (fun x hx y hy hxy =>
      hsep x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy) b 0 le_rfl
      (fun x hx => by
        have h1 := hsep b (Finset.mem_insert_self _ _) x (Finset.mem_insert_of_mem hx) (hb x hx).ne'
        rwa [abs_of_pos (by linarith only [hb x hx])] at h1)
    simp only [add_zero, mul_pow] at hdist
    rw [← Finset.sum_mul, sum_range_add_one_sq] at hdist
    rw [Finset.card_insert_of_notMem hbs, Finset.sum_insert hbs, Finset.sum_insert hbs]
    have hsplit : ∑ x ∈ s, (b - x) ^ 2 =
        (s.card : ℝ) * b ^ 2 - 2 * b * ∑ x ∈ s, x + ∑ x ∈ s, x ^ 2 := by
      have : ∀ x ∈ s, (b - x) ^ 2 = b ^ 2 - 2 * b * x + x ^ 2 := fun x _ => by ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    push_cast
    rw [hsplit] at hdist
    nlinarith only [hih, hdist, sq_nonneg μ]

/-! ## The spread of the Hermite roots -/

open Polynomial in
theorem eval_heatFlow_X_pow (k : ℕ) (σ : ℂ) :
    (heatFlow 1 ((X : ℂ[X]) ^ k)).eval σ = heatModelFwd k σ := by
  classical
  have hdeg : ((X : ℂ[X]) ^ k).natDegree = k := natDegree_X_pow k
  rw [heatFlow, hdeg, heatModelFwd, eval_finsetSum]
  have hsub : Finset.range (k / 2 + 1) ⊆ Finset.range (k + 1) := by
    intro m hm
    simp only [Finset.mem_range] at hm ⊢
    omega
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun m hm => ?_
    simp only [Finset.mem_range] at hm
    have hm2 : 2 * m ≤ k := by omega
    rw [eval_mul, eval_C, iterate_derivative_X_pow_eq_smul, eval_smul, eval_pow, eval_X]
    have hdesc := Nat.factorial_mul_descFactorial hm2
    have hdesc' : ((k.descFactorial (2 * m) : ℕ) : ℂ) =
        (k.factorial : ℂ) / ((k - 2 * m).factorial : ℂ) := by
      rw [eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero _), mul_comm]
      exact_mod_cast hdesc
    rw [smul_eq_mul, hdesc']
    have hf1 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hf2 : ((k - 2 * m).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp
  · intro m hm hm'
    simp only [Finset.mem_range] at hm hm'
    have hm2 : k < 2 * m := by omega
    rw [eval_mul, eval_C, iterate_derivative_X_pow_eq_smul, Nat.descFactorial_eq_zero_iff_lt.mpr hm2,
      Nat.cast_zero, zero_smul, eval_zero, mul_zero]

/-- The roots of `Q_k` have spread `2k²(k−1)`. -/
theorem spread_profileRoots {k : ℕ} (hk : 2 ≤ k) :
    (k : ℝ) * ∑ x ∈ profileRoots k, x ^ 2 - (∑ x ∈ profileRoots k, x) ^ 2 =
      2 * (k : ℝ) ^ 2 * ((k : ℝ) - 1) := by
  classical
  set q : ℂ[X] := heatFlow 1 ((X : ℂ[X]) ^ k) with hq
  have hmonic : ((X : ℂ[X]) ^ k).Monic := monic_X_pow k
  have hdeg : ((X : ℂ[X]) ^ k).natDegree = k := natDegree_X_pow k
  obtain ⟨hqm, hqd⟩ := heatFlow_monic (t := 1) hmonic
  have hspread := spread_roots_heatFlow hmonic (by rw [hdeg]; exact hk) 1
  have hq0 : q ≠ 0 := hqm.ne_zero
  set Z' := (profileRoots k).image (fun x : ℝ => (x : ℂ)) with hZ'
  have hinj : Function.Injective (fun x : ℝ => (x : ℂ)) := Complex.ofReal_injective
  have hcardZ' : Z'.card = k := by
    rw [hZ', Finset.card_image_of_injective _ hinj, card_profileRoots]
  have hle : Z'.val ≤ q.roots := by
    rw [Finset.val_le_iff_val_subset]
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_val.mp hz)
    refine (mem_roots hq0).mpr ?_
    rw [IsRoot.def, hq, eval_heatFlow_X_pow, heatModelFwd_ofReal, heatPoly_eq_zero_of_mem hx]
    simp
  have hcardq : Multiset.card q.roots = k := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hqd, hdeg]
  have heq : Z'.val = q.roots := Multiset.eq_of_le_of_card_le hle (by
    rw [hcardq]
    exact (show k ≤ Z'.card from hcardZ'.ge))
  have hzero : spread ((X : ℂ[X]) ^ k).roots = 0 := by
    simp [spread, roots_pow, roots_X, Multiset.map_nsmul, Multiset.sum_nsmul]
  rw [hzero, zero_add, hdeg, ← heq] at hspread
  have hsum1 : Z'.val.sum = ((∑ x ∈ profileRoots k, x : ℝ) : ℂ) := by
    rw [Finset.sum_val, hZ', Finset.sum_image fun a _ b _ h => hinj h, Complex.ofReal_sum]
    rfl
  have hsum2 : (Z'.val.map fun x => x ^ 2).sum = ((∑ x ∈ profileRoots k, x ^ 2 : ℝ) : ℂ) := by
    change ∑ z ∈ Z', z ^ 2 = _
    rw [hZ', Finset.sum_image fun a _ b _ h => hinj h]
    push_cast
    rfl
  have hcard' : Multiset.card Z'.val = k := hcardZ'
  rw [spread, hcard', hsum1, hsum2] at hspread
  have hcast : (((k : ℝ) * ∑ x ∈ profileRoots k, x ^ 2 - (∑ x ∈ profileRoots k, x) ^ 2 : ℝ) : ℂ) =
      ((2 * (k : ℝ) ^ 2 * ((k : ℝ) - 1) : ℝ) : ℂ) := by
    push_cast
    push_cast at hspread
    rw [hspread]
    ring
  exact_mod_cast hcast

/-- **The Hermite mesh.** Two roots of `Q_k` lie within `μ`, with `μ² ≤ 24/(k+1)`. -/
theorem exists_close_profileRoots {k : ℕ} (hk : 2 ≤ k) :
    ∃ ρ ∈ profileRoots k, ∃ ρ' ∈ profileRoots k, ρ ≠ ρ' ∧ (ρ - ρ') ^ 2 ≤ 24 / ((k : ℝ) + 1) := by
  classical
  have hcard := card_profileRoots k
  have hne : (profileRoots k).offDiag.Nonempty := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by rw [hcard]; omega :
      1 < (profileRoots k).card)
    exact ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩⟩
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image _ (fun p : ℝ × ℝ => |p.1 - p.2|) hne
  obtain ⟨hp1, hp2, hp3⟩ := Finset.mem_offDiag.mp hp
  refine ⟨p.1, hp1, p.2, hp2, hp3, ?_⟩
  set μ := |p.1 - p.2| with hμ
  have hsep : ∀ x ∈ profileRoots k, ∀ y ∈ profileRoots k, x ≠ y → μ ≤ |x - y| := fun x hx y hy hxy =>
    hmin (x, y) (Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩)
  have hpack := spread_ge_of_sep (abs_nonneg _) _ hsep
  rw [hcard, spread_profileRoots hk] at hpack
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hsq : (p.1 - p.2) ^ 2 = μ ^ 2 := by rw [hμ, sq_abs]
  rw [hsq, le_div_iff₀ (by linarith only [hk2])]
  -- `μ² k²(k²−1)/12 ≤ 2k²(k−1)` divided by `k²(k−1)/12`
  have hfac : (0 : ℝ) < (k : ℝ) ^ 2 * ((k : ℝ) - 1) := by
    apply mul_pos (by positivity)
    linarith only [hk2]
  have heq : μ ^ 2 * ((k : ℝ) ^ 2 * ((k : ℝ) ^ 2 - 1) / 12) =
      ((k : ℝ) ^ 2 * ((k : ℝ) - 1)) * (μ ^ 2 * ((k : ℝ) + 1) / 12) := by ring
  have heq2 : 2 * (k : ℝ) ^ 2 * ((k : ℝ) - 1) = ((k : ℝ) ^ 2 * ((k : ℝ) - 1)) * 2 := by ring
  rw [heq, heq2] at hpack
  have := le_of_mul_le_mul_left hpack hfac
  linarith only [this]

/-- **Hermite gaps above a zero of order `k`.** Above a real zero of exact order `k ≥ 2` two real zeros
satisfy `g² ≤ (24/(k+1) + ε)(t − t₀)`. -/
theorem exists_close_zeros_forward {s : ℝ} (hs : 0 ≤ s) {x₀ : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hvan : ∀ i < k, iteratedDeriv i (riemannHeat s) x₀ = 0)
    (ha : iteratedDeriv k (riemannHeat s) x₀ ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₁ > 0, ∀ q, 0 < q → q ≤ q₁ → ∃ y y' : ℝ, y < y' ∧
      riemannHeat (s + q ^ 2) (y : ℂ) = 0 ∧ riemannHeat (s + q ^ 2) (y' : ℂ) = 0 ∧
      |y - x₀| + |y' - x₀| ≤ (∑ ρ ∈ profileRoots k, |ρ| + 2) * q ∧
      (y' - y) ^ 2 ≤ (24 / ((k : ℝ) + 1) + ε) * q ^ 2 := by
  classical
  obtain ⟨ρ, hρ, ρ', hρ', hne, hclose⟩ := exists_close_profileRoots hk
  wlog hlt : ρ < ρ' generalizing ρ ρ'
  · exact this ρ' hρ' ρ hρ hne.symm (by rw [show (ρ' - ρ) ^ 2 = (ρ - ρ') ^ 2 by ring]; exact hclose)
      (lt_of_le_of_ne (not_lt.mp hlt) hne.symm)
  set μ := ρ' - ρ with hμ
  have hμpos : 0 < μ := sub_pos.mpr hlt
  -- a precision so small that the two zeros stay ordered and close
  set e := min (min 1 (μ / 4)) (ε / (8 * (μ + 1))) with he
  have hepos : 0 < e := lt_min (lt_min one_pos (by positivity)) (by positivity)
  have he1 : e ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have he2 : e ≤ μ / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have he3 : e ≤ ε / (8 * (μ + 1)) := min_le_right _ _
  obtain ⟨q₁, hq₁, hnear⟩ := exists_zero_near_root_forward hs hvan ha hepos
  refine ⟨q₁, hq₁, fun q hq hqq => ?_⟩
  obtain ⟨y, hy, hy0⟩ := hnear q hq hqq ρ hρ
  obtain ⟨y', hy', hy0'⟩ := hnear q hq hqq ρ' hρ'
  obtain ⟨h1, h2⟩ := abs_le.mp hy
  obtain ⟨h3, h4⟩ := abs_le.mp hy'
  have hμq : (y' - y) ≤ (μ + 2 * e) * q := by
    rw [hμ]
    nlinarith only [h2, h3, h1, h4]
  have hμq' : (μ - 2 * e) * q ≤ y' - y := by
    rw [hμ]
    nlinarith only [h2, h3, h1, h4]
  have hposgap : 0 < (μ - 2 * e) * q := mul_pos (by linarith only [he2, hμpos]) hq
  refine ⟨y, y', by linarith only [hμq', hposgap], hy0, hy0', ?_, ?_⟩
  · have hρle : |ρ| + |ρ'| ≤ ∑ r ∈ profileRoots k, |r| := by
      have hsub : ({ρ, ρ'} : Finset ℝ) ⊆ profileRoots k := by
        intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact hρ
        · rw [Finset.mem_singleton.mp hr]
          exact hρ'
      have h5 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun r => |r|) hsub
        (fun _ _ _ => abs_nonneg _)
      rwa [Finset.sum_pair hne] at h5
    have ha1 : |y - x₀| ≤ |ρ| * q + e * q := by
      have : y - x₀ = (y - (x₀ + q * ρ)) + q * ρ := by ring
      rw [this]
      calc _ ≤ |y - (x₀ + q * ρ)| + |q * ρ| := abs_add_le _ _
        _ ≤ e * q + |q * ρ| := by gcongr
        _ = _ := by rw [abs_mul, abs_of_pos hq]; ring
    have ha2 : |y' - x₀| ≤ |ρ'| * q + e * q := by
      have : y' - x₀ = (y' - (x₀ + q * ρ')) + q * ρ' := by ring
      rw [this]
      calc _ ≤ |y' - (x₀ + q * ρ')| + |q * ρ'| := abs_add_le _ _
        _ ≤ e * q + |q * ρ'| := by gcongr
        _ = _ := by rw [abs_mul, abs_of_pos hq]; ring
    nlinarith only [ha1, ha2, hρle, hq, he1, mul_le_mul_of_nonneg_right he1 hq.le]
  · have hsq := pow_le_pow_left₀ (by linarith only [hμq', hposgap] : 0 ≤ y' - y) hμq 2
    have hq2 : 0 ≤ q ^ 2 := by positivity
    have hexp : (μ + 2 * e) ^ 2 ≤ μ ^ 2 + ε := by
      have hmul : 8 * (μ + 1) * e ≤ ε := by
        have := (le_div_iff₀ (by positivity : 0 < 8 * (μ + 1))).mp he3
        linarith only [this]
      nlinarith only [hmul, hepos, he1, hμpos]
    have hμ2 : μ ^ 2 ≤ 24 / ((k : ℝ) + 1) := by
      rw [hμ, show (ρ' - ρ) ^ 2 = (ρ - ρ') ^ 2 by ring]
      exact hclose
    calc (y' - y) ^ 2 ≤ ((μ + 2 * e) * q) ^ 2 := hsq
      _ = (μ + 2 * e) ^ 2 * q ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hexp, hμ2]) hq2

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
