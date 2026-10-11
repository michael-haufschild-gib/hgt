import GaloisForLFunctions.RHTower.ZetaNarrowLorentzMass
import GaloisForLFunctions.RHTower.ZetaRigidOrdinateWindow
import GaloisForLFunctions.HTGeometry.LorentzOrderedSums

/-!
# Local structure of rigid zeros under count control

Write `γ_n` for the ordered positive ordinates, `g_n = γ_{n+1} − γ_n`, and
`M_τ(p) = Σ_ρ τ²/(τ² + (p − γ)²)` for the narrow mass. Count control at `p` at scale `τ` means
`(1 − δ)τℓ/2 ≤ M_τ(p) ≤ (1 + δ)τℓ/2`.

**Theorem** (`window_structure`). Let `0 < τ₁ ≤ τ₂ ≤ 1`, `t > 13τ₂`, and
`(1 + δ)τ₁²ℓ/τ₂ < (1 − δ)τ₁ℓ/2`. Assume count control at both scales at the grid points
`t + 2jτ₂`, `|j| ≤ 6`, and `h`-rigidity at every index with `|γ_k − t| ≤ 8τ₂`. Put `η = 40τ₂/h`. Then:

* every gap `g_m` with `|γ_m − t| ≤ 8τ₂` is `< 4τ₂`;
* any two such gaps satisfy `g_{m'} ≤ g_m e^η`;
* there are indices `a ≤ b` with `γ_a ∈ (t − 7τ₂, t − 5τ₂)` and `γ_b ∈ (t + 5τ₂, t + 7τ₂)`;
* every such gap satisfies `(1 − δ)τ₁ℓ/2 − (1 + δ)τ₁²ℓ/τ₂ − 2 ≤ πτ₁e^η/g_m` (sparse Lorentz sum) and
  `2τ₁/(g_m e^η) − 1 ≤ (1 + δ)τ₁ℓ` (dense count).

A single point is not enough. A half-lattice of density `2ρ` ending at `t` has the same masses at `t` as a
lattice of density `ρ` at every scale. The grid detects any gap `≥ 4τ₂`: such a gap contains a grid
point `p` with no zero within `τ₂`, and there `M_{τ₁}(p) ≤ 2(τ₁/τ₂)² M_{τ₂}(p)` is too small.
-/

noncomputable section

open Complex Finset
open GaloisForLFunctions.HTGeometry (lorentzF lorentzF_nonneg lorentzF_le_tail sum_lorentz_sparse_le
  card_le_two_mul_sum_lorentz card_near_ge_of_dense)

namespace RHTower

/-- Two-sided count control `(1 − δ)τℓ/2 ≤ M_τ(p) ≤ (1 + δ)τℓ/2`. -/
def CountControl (τ ℓ δ p : ℝ) : Prop :=
  (1 - δ) * (τ * ℓ / 2) ≤ narrowMass τ p ∧ narrowMass τ p ≤ (1 + δ) * (τ * ℓ / 2)

theorem narrowMassTerm_eq_lorentzF (τ p : ℝ) (q : XiZeroCopy) :
    narrowMassTerm τ p q = lorentzF τ (p - (q.1 : ℂ).im) := rfl

/-- Sums over ordered indices are bounded by the narrow mass. -/
theorem sum_lorentzF_ordinate_le_narrowMass {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (S : Finset ℕ)
    (p : ℝ) : ∑ n ∈ S, lorentzF τ (p - xiOrderedPositiveOrdinate n) ≤ narrowMass τ p := by
  have e : ∑ n ∈ S, lorentzF τ (p - xiOrderedPositiveOrdinate n) =
      ∑ q ∈ S.map ⟨xiOrderedPositiveZeroCopy, xiOrderedPositiveZeroCopy_injective⟩,
        narrowMassTerm τ p q := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Function.Embedding.coeFn_mk, narrowMassTerm_eq_lorentzF,
      xiOrderedPositiveZeroCopy_im_eq]
  rw [e]
  exact (summable_narrowMassTerm hτ0.le hτ1 p).sum_le_tsum _
    (fun q _ => narrowMassTerm_nonneg τ p q)

/-- **Mass split.** If every copy outside the ordered indices of `S` is at distance `≥ σ` from `p`,
then `M_τ(p) ≤ Σ_{n ∈ S} f_τ(p − γ_n) + 2(τ/σ)² M_σ(p)`. -/
theorem narrowMass_le_sum_add_tail {τ σ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hσ0 : 0 < σ)
    (hσ1 : σ ≤ 1) (S : Finset ℕ) (p : ℝ)
    (hfar : ∀ q : XiZeroCopy, (∀ n ∈ S, xiOrderedPositiveZeroCopy n ≠ q) →
      σ ≤ |p - (q.1 : ℂ).im|) :
    narrowMass τ p ≤ ∑ n ∈ S, lorentzF τ (p - xiOrderedPositiveOrdinate n) +
      2 * (τ / σ) ^ 2 * narrowMass σ p := by
  classical
  set F := S.map ⟨xiOrderedPositiveZeroCopy, xiOrderedPositiveZeroCopy_injective⟩ with hF
  have hsum : ∑ n ∈ S, lorentzF τ (p - xiOrderedPositiveOrdinate n) =
      ∑ q ∈ F, narrowMassTerm τ p q := by
    rw [hF, Finset.sum_map]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Function.Embedding.coeFn_mk, narrowMassTerm_eq_lorentzF,
      xiOrderedPositiveZeroCopy_im_eq]
  have hs1 := summable_narrowMassTerm hτ0.le hτ1 p
  have hs2 := summable_narrowMassTerm hσ0.le hσ1 p
  unfold narrowMass
  rw [← hs1.sum_add_tsum_compl (s := F), hsum]
  gcongr
  have hpt : ∀ q : ↑((F : Set XiZeroCopy)ᶜ), narrowMassTerm τ p q ≤
      2 * (τ / σ) ^ 2 * narrowMassTerm σ p q := by
    rintro ⟨q, hq⟩
    simp only [narrowMassTerm_eq_lorentzF]
    refine lorentzF_le_tail hτ0 hσ0 (hfar q fun n hn h => hq ?_)
    rw [Finset.mem_coe, hF, Finset.mem_map]
    exact ⟨n, hn, h⟩
  calc ∑' q : ↑((F : Set XiZeroCopy)ᶜ), narrowMassTerm τ p q
      ≤ ∑' q : ↑((F : Set XiZeroCopy)ᶜ), 2 * (τ / σ) ^ 2 * narrowMassTerm σ p q :=
        (hs1.subtype _).tsum_le_tsum hpt ((hs2.subtype _).mul_left _)
    _ = 2 * (τ / σ) ^ 2 * ∑' q : ↑((F : Set XiZeroCopy)ᶜ), narrowMassTerm σ p q := tsum_mul_left
    _ ≤ 2 * (τ / σ) ^ 2 * ∑' q, narrowMassTerm σ p q := by
        gcongr
        exact Summable.tsum_subtype_le (narrowMassTerm σ p) _ (narrowMassTerm_nonneg σ p) hs2

/-- A positive copy is an ordered copy. -/
theorem exists_index_of_im_pos {q : XiZeroCopy} (hq : 0 < (q.1 : ℂ).im) :
    ∃ n, xiOrderedPositiveZeroCopy n = q :=
  exists_xiOrderedPositiveZeroCopy_eq hq

/-- **A controlled point has a zero within `τ₂`.** -/
theorem exists_ordinate_near_of_countControl {τ₁ τ₂ ℓ δ p : ℝ} (hτ₁ : 0 < τ₁) (hτ₁₂ : τ₁ ≤ τ₂)
    (hτ₂1 : τ₂ ≤ 1) (hp : τ₂ < p)
    (hnum : (1 + δ) * τ₁ ^ 2 * ℓ / τ₂ < (1 - δ) * (τ₁ * ℓ / 2))
    (h₁ : CountControl τ₁ ℓ δ p) (h₂ : CountControl τ₂ ℓ δ p) :
    ∃ n, |xiOrderedPositiveOrdinate n - p| < τ₂ := by
  by_contra hcon
  push Not at hcon
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ₁₂
  have hfar : ∀ q : XiZeroCopy, (∀ n ∈ (∅ : Finset ℕ), xiOrderedPositiveZeroCopy n ≠ q) →
      τ₂ ≤ |p - (q.1 : ℂ).im| := by
    intro q _
    rcases le_or_gt ((q.1 : ℂ).im) 0 with hq | hq
    · rw [abs_of_pos (by linarith)]; linarith
    · obtain ⟨n, rfl⟩ := exists_index_of_im_pos hq
      rw [xiOrderedPositiveZeroCopy_im_eq, abs_sub_comm]
      exact hcon n
  have hsplit := narrowMass_le_sum_add_tail hτ₁ (hτ₁₂.trans hτ₂1) hτ₂ hτ₂1 ∅ p hfar
  rw [Finset.sum_empty, zero_add] at hsplit
  have h1 := h₁.1
  have h2 := h₂.2
  have : 2 * (τ₁ / τ₂) ^ 2 * narrowMass τ₂ p ≤ 2 * (τ₁ / τ₂) ^ 2 * ((1 + δ) * (τ₂ * ℓ / 2)) := by
    gcongr
  have e : 2 * (τ₁ / τ₂) ^ 2 * ((1 + δ) * (τ₂ * ℓ / 2)) = (1 + δ) * τ₁ ^ 2 * ℓ / τ₂ := by
    field_simp
  linarith


/-- **No gap of length `4τ₂` near `t`** when every grid point `t + 2jτ₂`, `|j| ≤ 6`, has a zero
within `τ₂`. -/
theorem ordinateGap_lt_of_grid {t τ₂ : ℝ} (hτ₂ : 0 < τ₂)
    (hgrid : ∀ j : ℤ, |j| ≤ 6 → ∃ n, |xiOrderedPositiveOrdinate n - (t + 2 * j * τ₂)| < τ₂)
    {m : ℕ} (hm : |xiOrderedPositiveOrdinate m - t| ≤ 8 * τ₂) : ordinateGap m < 4 * τ₂ := by
  by_contra hcon
  push Not at hcon
  set γ := xiOrderedPositiveOrdinate with hγ
  set j : ℤ := ⌈(γ m + τ₂ - t) / (2 * τ₂)⌉ with hj
  have hj1 : (γ m + τ₂ - t) / (2 * τ₂) ≤ j := Int.le_ceil _
  have hj2 : (j : ℝ) < (γ m + τ₂ - t) / (2 * τ₂) + 1 := Int.ceil_lt_add_one _
  rw [div_le_iff₀ (by positivity)] at hj1
  rw [← sub_lt_iff_lt_add, lt_div_iff₀ (by positivity)] at hj2
  rw [abs_le] at hm
  have h3 : (-4 : ℝ) < j := by
    by_contra h; push Not at h
    have : (j : ℝ) * (2 * τ₂) ≤ -4 * (2 * τ₂) := mul_le_mul_of_nonneg_right h (by positivity)
    linarith
  have h4 : (j : ℝ) < 6 := by
    by_contra h; push Not at h
    have : 6 * (2 * τ₂) ≤ (j : ℝ) * (2 * τ₂) := mul_le_mul_of_nonneg_right h (by positivity)
    linarith
  have hjabs : |j| ≤ 6 := by
    have h3' : (-4 : ℤ) < j := by exact_mod_cast h3
    have h4' : j < 6 := by exact_mod_cast h4
    rw [abs_le]; constructor <;> omega
  obtain ⟨n, hn⟩ := hgrid j hjabs
  rw [abs_lt] at hn
  have hlo : γ m < γ n := by linarith
  have hhi : γ n < γ (m + 1) := by
    have : γ (m + 1) = γ m + ordinateGap m := by simp [ordinateGap, hγ]
    linarith
  rcases le_or_gt n m with hnm | hnm
  · linarith [xiOrderedPositiveOrdinate_monotone hnm]
  · linarith [xiOrderedPositiveOrdinate_monotone (show m + 1 ≤ n by omega)]

/-- **Gap ratios in the window.** -/
theorem ordinateGap_le_mul_exp_of_window {t τ₂ h : ℝ} (hh : 0 < h)
    (hrig : ∀ k, |xiOrderedPositiveOrdinate k - t| ≤ 8 * τ₂ → RigidAt h k)
    (hsmall : ∀ m, |xiOrderedPositiveOrdinate m - t| ≤ 8 * τ₂ → ordinateGap m < 4 * τ₂)
    {m m' : ℕ} (hm : |xiOrderedPositiveOrdinate m - t| ≤ 8 * τ₂)
    (hm' : |xiOrderedPositiveOrdinate m' - t| ≤ 8 * τ₂) :
    ordinateGap m' ≤ ordinateGap m * Real.exp (40 * τ₂ / h) := by
  set γ := xiOrderedPositiveOrdinate with hγ
  have hin : ∀ {u v k : ℕ}, |γ u - t| ≤ 8 * τ₂ → |γ v - t| ≤ 8 * τ₂ → u ≤ k → k ≤ v →
      |γ k - t| ≤ 8 * τ₂ := by
    intro u v k hu hv huk hkv
    have h1 := xiOrderedPositiveOrdinate_monotone huk
    have h2 := xiOrderedPositiveOrdinate_monotone hkv
    rw [abs_le] at hu hv ⊢
    constructor <;> linarith
  have hE : 2 * (20 * τ₂) / h = 40 * τ₂ / h := by ring
  rcases le_total m m' with hmm | hmm
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmm
    have hD : γ (m + j + 1) - γ m ≤ 20 * τ₂ := by
      have hg := hsmall (m + j) hm'
      have : γ (m + j + 1) = γ (m + j) + ordinateGap (m + j) := by simp [ordinateGap, hγ]
      rw [abs_le] at hm hm'
      linarith
    have := (gap_chain_span_local hh j (fun k hk1 hk2 => hrig k (hin hm hm' hk1 hk2.le)) hD).1
    rwa [hE] at this
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmm
    have hD : γ (m' + j + 1) - γ m' ≤ 20 * τ₂ := by
      have hg := hsmall (m' + j) hm
      have : γ (m' + j + 1) = γ (m' + j) + ordinateGap (m' + j) := by simp [ordinateGap, hγ]
      rw [abs_le] at hm hm'
      linarith
    have := (gap_chain_span_local hh j (fun k hk1 hk2 => hrig k (hin hm' hm hk1 hk2.le)) hD).2
    rwa [hE] at this

/-- **Local structure of rigid zeros under count control.** -/
theorem window_structure {t τ₁ τ₂ ℓ δ h : ℝ} (hτ₁ : 0 < τ₁) (hτ₁₂ : τ₁ ≤ τ₂) (hτ₂1 : τ₂ ≤ 1)
    (hh : 0 < h) (ht : 13 * τ₂ < t)
    (hnum : (1 + δ) * τ₁ ^ 2 * ℓ / τ₂ < (1 - δ) * (τ₁ * ℓ / 2))
    (hC : ∀ j : ℤ, |j| ≤ 6 →
      CountControl τ₁ ℓ δ (t + 2 * j * τ₂) ∧ CountControl τ₂ ℓ δ (t + 2 * j * τ₂))
    (hrig : ∀ k, |xiOrderedPositiveOrdinate k - t| ≤ 8 * τ₂ → RigidAt h k) :
    (∀ m, |xiOrderedPositiveOrdinate m - t| ≤ 8 * τ₂ → ordinateGap m < 4 * τ₂) ∧
    (∀ m m', |xiOrderedPositiveOrdinate m - t| ≤ 8 * τ₂ →
      |xiOrderedPositiveOrdinate m' - t| ≤ 8 * τ₂ →
      ordinateGap m' ≤ ordinateGap m * Real.exp (40 * τ₂ / h)) ∧
    (∃ a b : ℕ, a ≤ b ∧ t - 7 * τ₂ < xiOrderedPositiveOrdinate a ∧
      xiOrderedPositiveOrdinate a < t - 5 * τ₂ ∧ t + 5 * τ₂ < xiOrderedPositiveOrdinate b ∧
      xiOrderedPositiveOrdinate b < t + 7 * τ₂) ∧
    (∀ m, |xiOrderedPositiveOrdinate m - t| ≤ 8 * τ₂ →
      (1 - δ) * (τ₁ * ℓ / 2) - (1 + δ) * τ₁ ^ 2 * ℓ / τ₂ - 2 ≤
        Real.pi * τ₁ * Real.exp (40 * τ₂ / h) / ordinateGap m) ∧
    (∀ m, |xiOrderedPositiveOrdinate m - t| ≤ 8 * τ₂ →
      2 * τ₁ / (ordinateGap m * Real.exp (40 * τ₂ / h)) - 1 ≤ (1 + δ) * (τ₁ * ℓ)) := by
  classical
  set γ := xiOrderedPositiveOrdinate with hγ
  set η := 40 * τ₂ / h with hη
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ₁₂
  have hgrid : ∀ j : ℤ, |j| ≤ 6 → ∃ n, |γ n - (t + 2 * j * τ₂)| < τ₂ := by
    intro j hj
    have hj' : (-6 : ℝ) ≤ j := by
      have : -6 ≤ j := (abs_le.mp hj).1
      exact_mod_cast this
    refine exists_ordinate_near_of_countControl hτ₁ hτ₁₂ hτ₂1 (by nlinarith) hnum
      (hC j hj).1 (hC j hj).2
  have hsmall : ∀ m, |γ m - t| ≤ 8 * τ₂ → ordinateGap m < 4 * τ₂ :=
    fun m hm => ordinateGap_lt_of_grid hτ₂ hgrid hm
  have hratio : ∀ m m', |γ m - t| ≤ 8 * τ₂ → |γ m' - t| ≤ 8 * τ₂ →
      ordinateGap m' ≤ ordinateGap m * Real.exp η :=
    fun m m' hm hm' => ordinateGap_le_mul_exp_of_window hh hrig hsmall hm hm'
  obtain ⟨a, ha⟩ := hgrid (-3) (by norm_num)
  obtain ⟨b, hb⟩ := hgrid 3 (by norm_num)
  push_cast at ha hb
  rw [abs_lt] at ha hb
  have hab : a ≤ b := by
    by_contra hc; push Not at hc
    have := xiOrderedPositiveOrdinate_monotone hc.le
    linarith
  have hcov : ∃ a b : ℕ, a ≤ b ∧ t - 7 * τ₂ < γ a ∧ γ a < t - 5 * τ₂ ∧ t + 5 * τ₂ < γ b ∧
      γ b < t + 7 * τ₂ := ⟨a, b, hab, by linarith, by linarith, by linarith, by linarith⟩
  have hwin : ∀ k, a ≤ k → k ≤ b → |γ k - t| ≤ 8 * τ₂ := by
    intro k hk1 hk2
    have h1 := xiOrderedPositiveOrdinate_monotone hk1
    have h2 := xiOrderedPositiveOrdinate_monotone hk2
    rw [abs_le]; constructor <;> linarith
  have hgpos : ∀ m, |γ m - t| ≤ 8 * τ₂ → 0 < ordinateGap m := by
    intro m hm
    have := (hrig m hm).1
    simp only [ordinateGap] at this ⊢
    linarith
  have hC0 := hC 0 (by norm_num)
  simp only [Int.cast_zero, mul_zero, zero_mul, add_zero] at hC0
  refine ⟨hsmall, hratio, hcov, fun m hm => ?_, fun m hm => ?_⟩
  · -- sparse upper bound
    have hgm := hgpos m hm
    have hG : 0 < ordinateGap m * Real.exp (-η) := by positivity
    have hgap : ∀ n, a ≤ n → n < b → ordinateGap m * Real.exp (-η) ≤ γ (n + 1) - γ n := by
      intro n hn1 hn2
      have := hratio n m (hwin n hn1 hn2.le) hm
      have e : γ (n + 1) - γ n = ordinateGap n := rfl
      rw [e]
      calc ordinateGap m * Real.exp (-η) ≤ ordinateGap n * Real.exp η * Real.exp (-η) :=
            mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
        _ = ordinateGap n := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
            mul_one]
    have hsp := sum_lorentz_sparse_le hτ₁ hG hgap t
    have hfar : ∀ q : XiZeroCopy, (∀ n ∈ Finset.Icc a b, xiOrderedPositiveZeroCopy n ≠ q) →
        τ₂ ≤ |t - (q.1 : ℂ).im| := by
      intro q hq
      rcases le_or_gt ((q.1 : ℂ).im) 0 with hq0 | hq0
      · rw [abs_of_pos (by linarith)]; linarith
      · obtain ⟨k, rfl⟩ := exists_index_of_im_pos hq0
        rw [xiOrderedPositiveZeroCopy_im_eq]
        have hk : k ∉ Finset.Icc a b := fun hk => hq k hk rfl
        rw [Finset.mem_Icc] at hk
        rcases lt_or_ge k a with hka | hka
        · have := xiOrderedPositiveOrdinate_monotone hka.le
          rw [abs_of_pos (by linarith)]; linarith
        · have hkb : b < k := by omega
          have := xiOrderedPositiveOrdinate_monotone hkb.le
          rw [abs_of_neg (by linarith)]; linarith
    have hsplit := narrowMass_le_sum_add_tail hτ₁ (hτ₁₂.trans hτ₂1) hτ₂ hτ₂1 (Finset.Icc a b) t hfar
    have h1 := hC0.1.1
    have h2 := hC0.2.2
    have h3 : 2 * (τ₁ / τ₂) ^ 2 * narrowMass τ₂ t ≤ (1 + δ) * τ₁ ^ 2 * ℓ / τ₂ := by
      have e : 2 * (τ₁ / τ₂) ^ 2 * ((1 + δ) * (τ₂ * ℓ / 2)) = (1 + δ) * τ₁ ^ 2 * ℓ / τ₂ := by
        field_simp
      rw [← e]; gcongr
    have e2 : Real.pi * τ₁ / (ordinateGap m * Real.exp (-η)) =
        Real.pi * τ₁ * Real.exp η / ordinateGap m := by
      rw [Real.exp_neg]; field_simp
    rw [e2] at hsp
    linarith
  · -- dense lower bound
    have hgm := hgpos m hm
    have hg : 0 < ordinateGap m * Real.exp η := by positivity
    have hgap : ∀ n, a ≤ n → n < b → γ (n + 1) - γ n ≤ ordinateGap m * Real.exp η :=
      fun n hn1 hn2 => hratio m n hm (hwin n hn1 hn2.le)
    have hd := card_near_ge_of_dense hτ₁ hg xiOrderedPositiveOrdinate_monotone hgap
      (t := t) (by linarith) (by linarith)
    have hc := card_le_two_mul_sum_lorentz hτ₁ (Finset.Icc a b) γ t
    have hs := sum_lorentzF_ordinate_le_narrowMass hτ₁ (hτ₁₂.trans hτ₂1) (Finset.Icc a b) t
    have h2 := hC0.1.2
    have : 2 * τ₁ / (ordinateGap m * Real.exp η) - 1 ≤ 2 * narrowMass τ₁ t := by linarith
    linarith

end RHTower
