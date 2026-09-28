import GaloisForLFunctions.RHTower.XiZeroShortWeightBox

/-!
# The zero weight summed over all heights

Split the zeros into the finitely many with `|γ| < T₀` and the dyadic shells
`T₀ 2^k ≤ |γ| < T₀ 2^{k+1}`.  On each shell the box bound applies.  Shells below `X = x^{2u}` number
at most `1 + log X/log 2`, each carrying the zero-free saving `x^{-(1-uA) w(X)}`; shells above `X`
carry the decay `(x^u/T)^{2-A/2}`, which after absorbing `(1 + log T)^B ≤ P T^{c₁/4}` sums
geometrically to `P x^{-u c₁/4}/(1 - 2^{-c₁/8})`.  The result is an explicit majorant of
`Σ_ρ x^{β-1} min(1, c x^{2u}/(|ρ||1-ρ|))` valid for every `x ≥ 1`.
-/

namespace RHTower

noncomputable section

open Complex Finset

/-- Dyadic shells below `X` are few. -/
theorem card_dyadic_filter_le {T₀ X : ℝ} (hT₀ : 1 ≤ T₀) (hX : 1 ≤ X) (K : ℕ) :
    (((Finset.range K).filter fun k => T₀ * 2 ^ k ≤ X).card : ℝ) ≤ 1 + Real.log X / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnn : 0 ≤ Real.log X / Real.log 2 := div_nonneg (Real.log_nonneg hX) hlog2.le
  have hsub : ((Finset.range K).filter fun k => T₀ * 2 ^ k ≤ X)
      ⊆ Finset.range (⌊Real.log X / Real.log 2⌋₊ + 1) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [Finset.mem_range, Nat.lt_succ_iff]
    refine Nat.le_floor ?_
    rw [le_div_iff₀ hlog2]
    have h2k : (2 : ℝ) ^ k ≤ X := by
      have : (2 : ℝ) ^ k ≤ T₀ * 2 ^ k := le_mul_of_one_le_left (by positivity) hT₀
      linarith [hk.2]
    have := Real.log_le_log (by positivity) h2k
    rwa [Real.log_pow] at this
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  have : ((⌊Real.log X / Real.log 2⌋₊ + 1 : ℕ) : ℝ) ≤ 1 + Real.log X / Real.log 2 := by
    push_cast
    linarith [Nat.floor_le hnn]
  exact le_trans (by exact_mod_cast hcard) this

/-- A geometric sum over dyadic heights. -/
theorem sum_dyadic_rpow_neg_le {T₀ e : ℝ} (hT₀ : 1 ≤ T₀) (he : 0 < e) (K : ℕ) :
    ∑ k ∈ Finset.range K, (T₀ * 2 ^ k) ^ (-e) ≤ 1 / (1 - (2 : ℝ) ^ (-e)) := by
  have hr0 : 0 ≤ (2 : ℝ) ^ (-e) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ) ^ (-e) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hterm : ∀ k ∈ Finset.range K, (T₀ * 2 ^ k) ^ (-e) ≤ ((2 : ℝ) ^ (-e)) ^ k := by
    intro k _
    rw [Real.mul_rpow (by linarith) (by positivity)]
    have h1 : T₀ ^ (-e) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT₀ (by linarith)
    have h2 : ((2 : ℝ) ^ k) ^ (-e) = ((2 : ℝ) ^ (-e)) ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), mul_comm]
    rw [h2]
    exact mul_le_of_le_one_left (pow_nonneg hr0 _) h1
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have := geom_sum_Ico_le_of_lt_one (m := 0) (n := K) hr0 hr1
  rw [pow_zero, ← Finset.range_eq_Ico] at this
  exact this

/-- Polylogarithms are dominated by powers. -/
theorem one_add_log_pow_le_rpow (B : ℕ) {e : ℝ} (he : 0 < e) {T : ℝ} (hT : 1 ≤ T) :
    (1 + Real.log T) ^ B ≤ (1 + (B + 1) / e) ^ B * T ^ e := by
  have hT0 : 0 < T := by linarith
  set e' : ℝ := e / (B + 1) with he'
  have he'0 : 0 < e' := by positivity
  have hlog : 1 + Real.log T ≤ (1 + (B + 1) / e) * T ^ e' := by
    have h1 : Real.log (T ^ e') ≤ T ^ e' - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_rpow hT0] at h1
    have hTe : 1 ≤ T ^ e' := Real.one_le_rpow hT he'0.le
    have h2 : Real.log T ≤ (T ^ e' - 1) / e' := by
      rw [le_div_iff₀ he'0]
      linarith
    have h3 : (T ^ e' - 1) / e' ≤ (B + 1) / e * T ^ e' := by
      have heq : (B + 1) / e * T ^ e' = T ^ e' / e' := by
        rw [he']
        field_simp
      rw [heq]
      exact div_le_div_of_nonneg_right (by linarith) he'0.le
    nlinarith
  have hpow := pow_le_pow_left₀ (by linarith [Real.log_nonneg hT]) hlog B
  rw [mul_pow, ← Real.rpow_natCast (T ^ e'), ← Real.rpow_mul hT0.le] at hpow
  refine le_trans hpow (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine Real.rpow_le_rpow_of_exponent_le hT ?_
  rw [he']
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- Above `x^{2u}` the height factor beats `T^{c₁/4}` with room `x^{-uc₁/4} T^{-c₁/8}`. -/
theorem rpow_mul_heightFactor_le {x u c₁ T : ℝ} (hx : 1 ≤ x) (hc₁ : 0 ≤ c₁)
    (hT : x ^ (2 * u) ≤ T) (hT1 : 1 ≤ T) :
    T ^ (c₁ / 4) * (x ^ u / T) ^ c₁ ≤ x ^ (-(u * c₁ / 4)) * T ^ (-(c₁ / 8)) := by
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hq : 0 < x ^ u / T := div_pos (Real.rpow_pos_of_pos hx0 u) hT0
  have hτ : 2 * u * Real.log x ≤ Real.log T := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hT
    rwa [Real.log_rpow hx0] at this
  have hlogq : Real.log (x ^ u / T) = u * Real.log x - Real.log T := by
    rw [Real.log_div (Real.rpow_pos_of_pos hx0 u).ne' hT0.ne', Real.log_rpow hx0]
  rw [Real.rpow_def_of_pos hT0, Real.rpow_def_of_pos hq, hlogq, Real.rpow_def_of_pos hx0,
    Real.rpow_def_of_pos hT0, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have hℓ : 0 ≤ Real.log x := Real.log_nonneg hx
  nlinarith [mul_nonneg hc₁ (by linarith : 0 ≤ Real.log T - 2 * u * Real.log x)]

/-- The dyadic index `⌊log₂(|γ|/T₀)⌋`. -/
def dyadicHeightIndex (T₀ : ℝ) (q : XiZeroCopy) : ℕ := Nat.log 2 ⌊|(q.1 : ℂ).im| / T₀⌋₊

theorem dyadicHeightIndex_bounds {T₀ : ℝ} (hT₀ : 0 < T₀) {q : XiZeroCopy}
    (hq : T₀ ≤ |(q.1 : ℂ).im|) :
    T₀ * 2 ^ dyadicHeightIndex T₀ q ≤ |(q.1 : ℂ).im| ∧
      |(q.1 : ℂ).im| ≤ 2 * (T₀ * 2 ^ dyadicHeightIndex T₀ q) := by
  set y := |(q.1 : ℂ).im| / T₀ with hy
  have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ hT₀]; linarith
  have hfl : ⌊y⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy1)
    omega
  have hlow : 2 ^ dyadicHeightIndex T₀ q ≤ ⌊y⌋₊ := Nat.pow_log_le_self 2 hfl
  have hup : ⌊y⌋₊ < 2 ^ (dyadicHeightIndex T₀ q).succ := Nat.lt_pow_succ_log_self (by norm_num) _
  have hlowR : (2 : ℝ) ^ dyadicHeightIndex T₀ q ≤ y :=
    le_trans (by exact_mod_cast hlow) (Nat.floor_le (by linarith))
  have hupR : y ≤ 2 * 2 ^ dyadicHeightIndex T₀ q := by
    have h1 : (⌊y⌋₊ : ℝ) + 1 ≤ 2 ^ (dyadicHeightIndex T₀ q).succ := by exact_mod_cast hup
    have h2 := Nat.lt_floor_add_one y
    rw [pow_succ] at h1
    linarith
  rw [hy, le_div_iff₀ hT₀] at hlowR
  rw [hy, div_le_iff₀ hT₀] at hupR
  constructor <;> linarith

/-- **The majorant of the weighted zero sum.** -/
theorem tsum_zeroShortWeight_le {x u A c D T₀ P : ℝ} {B : ℕ} (w : ℝ → ℝ) (hx : 1 ≤ x)
    (hu : 0 ≤ u) (hA : 0 ≤ A) (hA4 : A < 4) (hδ : 0 ≤ 1 - u * A) (hc : 1 ≤ c) (hD : 0 ≤ D)
    (hT₀ : 1 ≤ T₀)
    (hP : ∀ T : ℝ, 1 ≤ T → (1 + Real.log T) ^ B ≤ P * T ^ ((2 - A / 2) / 4))
    (hdens : ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ((zeroHeightBox σ T).ncard : ℝ) ≤ D * (1 + Real.log T) ^ B * T ^ (A * (1 - σ)))
    (hfree : ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, (zeroHeightBox σ T).Nonempty → σ ≤ 1 - w T)
    (hw0 : ∀ T : ℝ, 0 ≤ w T) (hwanti : ∀ T T' : ℝ, T₀ ≤ T → T ≤ T' → w T' ≤ w T) :
    ∑' q : XiZeroCopy, zeroShortWeight x (c * x ^ (2 * u)) (q.1 : ℂ)
      ≤ ∑ q ∈ (finite_xiOrdinateWindow T₀ 0).toFinset, x ^ ((q.1 : ℂ).re - 1)
        + 4 * ((⌈Real.log x⌉₊ + 1 : ℕ) : ℝ) * c * D
          * x ^ (1 / (2 * ((⌈Real.log x⌉₊ + 1 : ℕ) : ℝ)))
          * ((1 + Real.log (x ^ (2 * u)) / Real.log 2) * (1 + Real.log (x ^ (2 * u))) ^ B
                * x ^ (-((1 - u * A) * w (x ^ (2 * u))))
              + P * x ^ (-(u * (2 - A / 2) / 4)) * (1 / (1 - (2 : ℝ) ^ (-((2 - A / 2) / 8))))) := by
  classical
  have hx0 : 0 < x := by linarith
  have hT₀0 : 0 < T₀ := by linarith
  set M : ℕ := ⌈Real.log x⌉₊ + 1 with hM
  have hM0 : 0 < M := by omega
  set c₁ : ℝ := 2 - A / 2 with hc₁
  have hc₁0 : 0 < c₁ := by rw [hc₁]; linarith
  set X := x ^ (2 * u) with hX
  have hX1 : 1 ≤ X := Real.one_le_rpow hx (by linarith)
  set δ := 1 - u * A with hδdef
  set Low := (finite_xiOrdinateWindow T₀ 0).toFinset with hLow
  set Cst := 4 * (M : ℝ) * c * D * x ^ (1 / (2 * (M : ℝ))) with hCst
  have hc0 : 0 ≤ c := by linarith
  have hCst0 : 0 ≤ Cst := by rw [hCst]; positivity
  set Q := (1 + Real.log X) ^ B * x ^ (-(δ * w X)) with hQ
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  set G := 1 / (1 - (2 : ℝ) ^ (-(c₁ / 8))) with hG
  have hG0 : 0 ≤ G := by
    rw [hG]
    have : (2 : ℝ) ^ (-(c₁ / 8)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have : 0 < 1 - (2 : ℝ) ^ (-(c₁ / 8)) := by linarith
    positivity
  have hP0 : 0 ≤ P := by
    have h := hP 1 le_rfl
    rw [Real.log_one, add_zero, one_pow, Real.one_rpow, mul_one] at h
    linarith
  have hY : 0 ≤ c * X := by positivity
  refine (summable_zeroShortWeight hx hY).tsum_le_of_sum_le fun F => ?_
  rw [← Finset.sum_filter_add_sum_filter_not F (fun q => |(q.1 : ℂ).im| < T₀)]
  -- the low zeros
  have hlow : ∑ q ∈ F with |(q.1 : ℂ).im| < T₀, zeroShortWeight x (c * X) (q.1 : ℂ)
      ≤ ∑ q ∈ Low, x ^ ((q.1 : ℂ).re - 1) := by
    have hsub : (F.filter fun q => |(q.1 : ℂ).im| < T₀) ⊆ Low := by
      intro q hq
      rw [Finset.mem_filter] at hq
      rw [hLow, Set.Finite.mem_toFinset, mem_xiOrdinateWindow_iff, sub_zero]
      exact hq.2.le
    refine le_trans (Finset.sum_le_sum fun q _ => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => Real.rpow_nonneg hx0.le _)
    rw [zeroShortWeight]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hx0.le _) (min_le_left _ _)
  -- the high zeros, shell by shell
  set Fh := F.filter fun q => ¬ |(q.1 : ℂ).im| < T₀ with hFh
  set K := Fh.sup (dyadicHeightIndex T₀) + 1 with hK
  have hmaps : ∀ q ∈ Fh, dyadicHeightIndex T₀ q ∈ Finset.range K := by
    intro q hq
    rw [Finset.mem_range, hK, Nat.lt_succ_iff]
    exact Finset.le_sup (f := dyadicHeightIndex T₀) hq
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  set f : ℕ → ℝ := fun k => (1 + Real.log (T₀ * 2 ^ k)) ^ B * x ^ (-(δ * w (T₀ * 2 ^ k)))
      * shortWeightHeightFactor x u c₁ (T₀ * 2 ^ k) with hf
  have hshell : ∀ k ∈ Finset.range K,
      ∑ q ∈ Fh with dyadicHeightIndex T₀ q = k, zeroShortWeight x (c * X) (q.1 : ℂ)
        ≤ Cst * f k := by
    intro k _
    have hTk : T₀ ≤ T₀ * 2 ^ k := le_mul_of_one_le_right hT₀0.le (one_le_pow₀ (by norm_num))
    have hbox := sum_zeroShortWeight_box_le (x := x) (u := u) (A := A) (c := c) (D := D)
      (w := w (T₀ * 2 ^ k)) (T := T₀ * 2 ^ k) (B := B) (M := M) hx hu hA hδ hc hD
      (hw0 _) (le_trans hT₀ hTk) hM0 (hdens _ hTk) (hfree _ hTk)
      (Fh.filter fun q => dyadicHeightIndex T₀ q = k) (by
        intro q hq
        rw [Finset.mem_filter, hFh, Finset.mem_filter] at hq
        have hq' : T₀ ≤ |(q.1 : ℂ).im| := le_of_not_gt hq.1.2
        have hb := dyadicHeightIndex_bounds hT₀0 hq'
        rw [hq.2] at hb
        exact hb)
    refine le_trans hbox (le_of_eq ?_)
    rw [hf, hCst]
    ring
  refine le_trans (add_le_add hlow (Finset.sum_le_sum hshell)) ?_
  refine add_le_add le_rfl ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hCst0
  -- split the shells at `X`
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range K) (fun k => T₀ * 2 ^ k ≤ X)]
  refine add_le_add ?_ ?_
  · -- shells below `X`
    have hterm : ∀ k ∈ (Finset.range K).filter (fun k => T₀ * 2 ^ k ≤ X), f k ≤ Q := by
      intro k hk
      rw [Finset.mem_filter] at hk
      have hTk : T₀ ≤ T₀ * 2 ^ k := le_mul_of_one_le_right hT₀0.le (one_le_pow₀ (by norm_num))
      have hTk1 : 1 ≤ T₀ * 2 ^ k := le_trans hT₀ hTk
      rw [hf, hQ]
      dsimp only
      have h1 : (1 + Real.log (T₀ * 2 ^ k)) ^ B ≤ (1 + Real.log X) ^ B :=
        pow_le_pow_left₀ (by linarith [Real.log_nonneg hTk1])
          (by linarith [Real.log_le_log (by linarith) hk.2]) B
      have h2 : x ^ (-(δ * w (T₀ * 2 ^ k))) ≤ x ^ (-(δ * w X)) :=
        Real.rpow_le_rpow_of_exponent_le hx
          (neg_le_neg (mul_le_mul_of_nonneg_left (hwanti _ _ hTk hk.2) hδ))
      have h3 := shortWeightHeightFactor_le_one hx0.le u hc₁0.le (T := T₀ * 2 ^ k)
      have h30 := shortWeightHeightFactor_nonneg hx0.le u c₁ (by linarith : (0 : ℝ) ≤ T₀ * 2 ^ k)
      calc (1 + Real.log (T₀ * 2 ^ k)) ^ B * x ^ (-(δ * w (T₀ * 2 ^ k)))
            * shortWeightHeightFactor x u c₁ (T₀ * 2 ^ k)
          ≤ (1 + Real.log X) ^ B * x ^ (-(δ * w X)) * 1 := by
            gcongr
        _ = (1 + Real.log X) ^ B * x ^ (-(δ * w X)) := mul_one _
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact le_of_le_of_eq (mul_le_mul_of_nonneg_right (card_dyadic_filter_le hT₀ hX1 K) hQ0)
      (by rw [hQ]; ring)
  · -- shells above `X`
    have hterm : ∀ k ∈ (Finset.range K).filter (fun k => ¬ T₀ * 2 ^ k ≤ X),
        f k ≤ P * x ^ (-(u * c₁ / 4)) * (T₀ * 2 ^ k) ^ (-(c₁ / 8)) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      have hXT : X < T₀ * 2 ^ k := lt_of_not_ge hk.2
      have hTk1 : 1 ≤ T₀ * 2 ^ k := by linarith
      have hxuX : x ^ u ≤ X := by
        rw [hX]
        exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      have hg : shortWeightHeightFactor x u c₁ (T₀ * 2 ^ k) = (x ^ u / (T₀ * 2 ^ k)) ^ c₁ := by
        rw [shortWeightHeightFactor, if_neg (by linarith)]
      rw [hf]
      dsimp only
      rw [hg]
      have hw1 : x ^ (-(δ * w (T₀ * 2 ^ k))) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hx (by nlinarith [hw0 (T₀ * 2 ^ k)])
      have hqk : 0 ≤ (x ^ u / (T₀ * 2 ^ k)) ^ c₁ := Real.rpow_nonneg (by positivity) _
      have hPk := hP _ hTk1
      have htail := rpow_mul_heightFactor_le hx hc₁0.le hXT.le hTk1
      have hlogk : 0 ≤ (1 + Real.log (T₀ * 2 ^ k)) ^ B := by
        have := Real.log_nonneg hTk1
        positivity
      calc (1 + Real.log (T₀ * 2 ^ k)) ^ B * x ^ (-(δ * w (T₀ * 2 ^ k)))
            * (x ^ u / (T₀ * 2 ^ k)) ^ c₁
          ≤ P * (T₀ * 2 ^ k) ^ (c₁ / 4) * 1 * (x ^ u / (T₀ * 2 ^ k)) ^ c₁ := by
            gcongr
        _ = P * ((T₀ * 2 ^ k) ^ (c₁ / 4) * (x ^ u / (T₀ * 2 ^ k)) ^ c₁) := by ring
        _ ≤ P * (x ^ (-(u * c₁ / 4)) * (T₀ * 2 ^ k) ^ (-(c₁ / 8))) :=
            mul_le_mul_of_nonneg_left htail hP0
        _ = P * x ^ (-(u * c₁ / 4)) * (T₀ * 2 ^ k) ^ (-(c₁ / 8)) := by ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hgeom : ∑ k ∈ (Finset.range K).filter (fun k => ¬ T₀ * 2 ^ k ≤ X),
        (T₀ * 2 ^ k) ^ (-(c₁ / 8)) ≤ G :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun k _ _ => Real.rpow_nonneg (by positivity) _)
        (sum_dyadic_rpow_neg_le hT₀ (by linarith) K)
    have hPx : 0 ≤ P * x ^ (-(u * c₁ / 4)) := mul_nonneg hP0 (Real.rpow_nonneg hx0.le _)
    calc P * x ^ (-(u * c₁ / 4)) * ∑ k ∈ (Finset.range K).filter (fun k => ¬ T₀ * 2 ^ k ≤ X),
          (T₀ * 2 ^ k) ^ (-(c₁ / 8))
        ≤ P * x ^ (-(u * c₁ / 4)) * G := mul_le_mul_of_nonneg_left hgeom hPx
      _ = P * x ^ (-(u * c₁ / 4)) * G := rfl
    
end

end RHTower
