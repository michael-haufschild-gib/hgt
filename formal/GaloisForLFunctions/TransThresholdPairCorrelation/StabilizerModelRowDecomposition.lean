import GaloisForLFunctions.TransThresholdPairCorrelation.StabilizerTaperTransport

/-!
# Literal odd-pair model as logarithmic rows

Symmetry groups ordered pairs into positive even shifts while retaining the
logarithmic aperture and upper integer endpoint. The exact row identity
separates the anchored taper from its endpoint variation. For fixed smooth
height profiles and aperture at most `log 2`, that variation has global cost
`C floor(X) O(Q) / T`, uniformly in the standard taper parameters.
-/

noncomputable section
open MeasureTheory Real Filter Topology Finset
open Zeta23 Zeta23.PrimeSide
namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-- Number of positive even shifts retained by the logarithmic aperture and
upper integer endpoint at a fixed base. -/
def stabilizerApertureLength (N : ℕ) (θ : ℝ) (m : ℕ) : ℕ :=
  (min N ⌊(m : ℝ) * Real.exp θ⌋₊ - m) / 2

private theorem weighted_pair_eq_upper (S : Finset ℕ) (K : ℕ → ℕ → ℝ) (f : ℕ → ℝ)
    (hsym : ∀ n m, K n m = K m n) (hdiag : ∀ n, K n n = 0) :
    (∑ n ∈ S, ∑ m ∈ S, K n m * f m) =
      ∑ n ∈ S, ∑ m ∈ S, if n < m then K n m * (f n + f m) else 0 := by
  have hsplit (n m : ℕ) : K n m * f m =
      (if n < m then K n m * f m else 0) + (if m < n then K n m * f m else 0) := by
    rcases lt_trichotomy n m with h | rfl | h
    · rw [if_pos h, if_neg (by omega), add_zero]
    · simp only [hdiag, zero_mul, lt_irrefl, if_false, add_zero]
    · rw [if_neg (by omega), if_pos h, zero_add]
  have hswap : (∑ n ∈ S, ∑ m ∈ S, if m < n then K n m * f m else 0) =
      ∑ n ∈ S, ∑ m ∈ S, if n < m then K n m * f n else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro n _
    apply sum_congr rfl
    intro m _
    rw [hsym m n]
  have hsum : (∑ n ∈ S, ∑ m ∈ S, K n m * f m) =
      (∑ n ∈ S, ∑ m ∈ S, if n < m then K n m * f m else 0) +
      ∑ n ∈ S, ∑ m ∈ S, if m < n then K n m * f m else 0 := by
    calc
      _ = ∑ n ∈ S, ∑ m ∈ S,
          ((if n < m then K n m * f m else 0) +
            (if m < n then K n m * f m else 0)) :=
        sum_congr rfl (fun n _ => sum_congr rfl (fun m _ => hsplit n m))
      _ = _ := by simp only [sum_add_distrib]
  rw [hsum, hswap, ← sum_add_distrib]
  apply sum_congr rfl
  intro n _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro m _
  split_ifs <;> ring

private theorem log_gap_le_iff_nat_le_floor {m n : ℕ} {θ : ℝ}
    (hm : 0 < m) (hn : m < n) :
    |Real.log n - Real.log m| ≤ θ ↔ n ≤ ⌊(m : ℝ) * Real.exp θ⌋₊ := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hnr : (0 : ℝ) < n := by exact_mod_cast hm.trans hn
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast hn.le
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hmr hmn)),
    ← Real.log_div hnr.ne' hmr.ne', Real.log_le_iff_le_exp (div_pos hnr hmr),
    div_le_iff₀ hmr, Nat.le_floor_iff (by positivity)]
  rw [mul_comm]

private theorem aperture_shift_mem_iff (N m r : ℕ) (θ : ℝ) :
    r < stabilizerApertureLength N θ m ↔
      m + 2 * (r + 1) ≤ N ∧ m + 2 * (r + 1) ≤ ⌊(m : ℝ) * Real.exp θ⌋₊ := by
  unfold stabilizerApertureLength
  omega

/-- Every retained shift is no larger than its base when the logarithmic
aperture is at most `log 2`. -/
theorem two_mul_stabilizerApertureLength_le (N m : ℕ) {θ : ℝ} (hθ : θ ≤ Real.log 2) :
    2 * stabilizerApertureLength N θ m ≤ m := by
  have hexp : Real.exp θ ≤ 2 := by
    have h := Real.exp_le_exp.mpr hθ
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  have hfloor : ⌊(m : ℝ) * Real.exp θ⌋₊ ≤ 2 * m := by
    have h := (Nat.floor_le (by positivity : 0 ≤ (m : ℝ) * Real.exp θ)).trans
      (mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg m))
    exact_mod_cast (by simpa only [mul_comm] using h :
      (⌊(m : ℝ) * Real.exp θ⌋₊ : ℝ) ≤ (2 : ℝ) * m)
  unfold stabilizerApertureLength
  omega

private def modelPairWeight (Q : ℕ) (Ω : ℝ → ℝ) (θ : ℝ) (n m : ℕ) : ℝ :=
  if 3 ≤ n ∧ 3 ≤ m ∧ n % 2 = 1 ∧ m % 2 = 1 ∧ n ≠ m ∧
      |Real.log n - Real.log m| ≤ θ then
    parityStabilizerWeight Q (Nat.dist n m) / (Real.sqrt n * Real.sqrt m) *
      cosTransform Ω (Real.log n - Real.log m)
  else 0

private theorem modelPairWeight_symm (Q : ℕ) (Ω : ℝ → ℝ) (θ : ℝ) (n m : ℕ) :
    modelPairWeight Q Ω θ n m = modelPairWeight Q Ω θ m n := by
  have hc : cosTransform Ω (Real.log m - Real.log n) =
      cosTransform Ω (Real.log n - Real.log m) := by
    rw [show Real.log m - Real.log n = -(Real.log n - Real.log m) by ring]
    simp only [cosTransform, mul_neg, Real.cos_neg]
  unfold modelPairWeight
  have hcond : (3 ≤ n ∧ 3 ≤ m ∧ n % 2 = 1 ∧ m % 2 = 1 ∧ n ≠ m ∧
      |Real.log n - Real.log m| ≤ θ) ↔
      (3 ≤ m ∧ 3 ≤ n ∧ m % 2 = 1 ∧ n % 2 = 1 ∧ m ≠ n ∧
      |Real.log m - Real.log n| ≤ θ) := by
    rw [abs_sub_comm (Real.log m), ne_comm (a := m) (b := n)]
    tauto
  simp only [← hcond]
  split_ifs
  · rw [Nat.dist_comm m n, mul_comm (Real.sqrt m), hc]
  · rfl

private theorem model_eq_upper (Q : ℕ) (Ω g : ℝ → ℝ) (X θ : ℝ) :
    stabilizerModelOddCoalSum Q Ω g X θ =
      (1 / (4 * π)) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        if n < m then modelPairWeight Q Ω θ n m * (g (Real.log n) + g (Real.log m)) else 0 := by
  have hscaled : stabilizerModelOddCoalSum Q Ω g X θ =
      (1 / (4 * π)) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        modelPairWeight Q Ω θ n m * g (Real.log m) := by
    unfold stabilizerModelOddCoalSum
    rw [mul_sum, mul_sum]
    apply sum_congr rfl
    intro n _
    rw [mul_sum, mul_sum]
    apply sum_congr rfl
    intro m _
    unfold modelPairWeight
    split_ifs <;> ring
  rw [hscaled, weighted_pair_eq_upper (primeRange X) (modelPairWeight Q Ω θ)
    (fun n => g (Real.log n)) (modelPairWeight_symm Q Ω θ)
    (fun n => by simp only [modelPairWeight, ne_self_iff_false, false_and, and_false, if_false])]

private theorem sum_aperture_reindex (N m : ℕ) (θ : ℝ) (F : ℕ → ℝ)
    (hm : 0 < m) (hmod : m % 2 = 1) :
    (∑ n ∈ (Ioc 0 N).filter (fun n => m < n ∧ n % 2 = 1 ∧
      |Real.log n - Real.log m| ≤ θ), F n) =
      ∑ r ∈ range (stabilizerApertureLength N θ m), F (m + 2 * (r + 1)) := by
  symm
  refine Finset.sum_nbij (fun r => m + 2 * (r + 1)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro r hr
    have hh := (aperture_shift_mem_iff N m r θ).mp (mem_range.mp hr)
    rw [mem_filter, mem_Ioc]
    refine ⟨⟨by omega, hh.1⟩, by omega, by omega, ?_⟩
    exact (log_gap_le_iff_nat_le_floor hm (by omega)).mpr hh.2
  · intro r₁ _ r₂ _ he
    change m + 2 * (r₁ + 1) = m + 2 * (r₂ + 1) at he
    omega
  · intro n hn
    simp only [mem_coe, mem_filter, mem_Ioc] at hn
    have hcap := (log_gap_le_iff_nat_le_floor hm hn.2.1).mp hn.2.2.2
    refine ⟨(n - m) / 2 - 1, ?_, ?_⟩
    · rw [mem_coe, mem_range, aperture_shift_mem_iff]
      omega
    · dsimp
      omega

private theorem upper_row_eq_logarithmic (Q N m : ℕ) (Ω g : ℝ → ℝ) (θ : ℝ)
    (hm3 : 3 ≤ m) (hmod : m % 2 = 1) :
    (∑ n ∈ Ioc 0 N, if m < n then
      modelPairWeight Q Ω θ m n * (g (Real.log m) + g (Real.log n)) else 0) =
      2 * g (Real.log m) * stabilizerLogarithmicRow Q Ω m (stabilizerApertureLength N θ m) +
        stabilizerTaperVariation Q Ω g m (stabilizerApertureLength N θ m) := by
  have hm : 0 < m := by omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  let F : ℕ → ℝ := fun n =>
    parityStabilizerWeight Q (Nat.dist m n) / (Real.sqrt m * Real.sqrt n) *
      cosTransform Ω (Real.log m - Real.log n) * (g (Real.log m) + g (Real.log n))
  have hfilter : (∑ n ∈ Ioc 0 N, if m < n then
      modelPairWeight Q Ω θ m n * (g (Real.log m) + g (Real.log n)) else 0) =
      ∑ n ∈ (Ioc 0 N).filter (fun n => m < n ∧ n % 2 = 1 ∧
        |Real.log n - Real.log m| ≤ θ), F n := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n _
    by_cases hmn : m < n
    · have hn3 : 3 ≤ n := by omega
      rw [if_pos hmn]
      by_cases hp : n % 2 = 1 ∧ |Real.log n - Real.log m| ≤ θ
      · have hfull : 3 ≤ m ∧ 3 ≤ n ∧ m % 2 = 1 ∧ n % 2 = 1 ∧ m ≠ n ∧
            |Real.log m - Real.log n| ≤ θ :=
          ⟨hm3, hn3, hmod, hp.1, hmn.ne, by rw [abs_sub_comm]; exact hp.2⟩
        rw [modelPairWeight, if_pos hfull, if_pos ⟨hmn, hp⟩]
      · have hfull : ¬ (3 ≤ m ∧ 3 ≤ n ∧ m % 2 = 1 ∧ n % 2 = 1 ∧ m ≠ n ∧
            |Real.log m - Real.log n| ≤ θ) := by
          rintro ⟨_, _, _, hnmod, _, hgap⟩
          exact hp ⟨hnmod, by rw [abs_sub_comm]; exact hgap⟩
        rw [modelPairWeight, if_neg hfull, if_neg (fun h => hp h.2), zero_mul]
    · rw [if_neg hmn, if_neg (fun h => hmn h.1)]
  rw [hfilter, sum_aperture_reindex N m θ F hm hmod]
  unfold stabilizerLogarithmicRow stabilizerTaperVariation
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro r _
  have hdist : Nat.dist m (m + 2 * (r + 1)) = 2 * (r + 1) := by
    rw [Nat.dist_eq_sub_of_le (by omega)]
    omega
  have hphase : Real.log ((m + 2 * (r + 1) : ℕ) : ℝ) - Real.log m =
      Real.log (1 + ((2 * (r + 1) : ℕ) : ℝ) / m) := by
    rw [← Real.log_div (by positivity : ((m + 2 * (r + 1) : ℕ) : ℝ) ≠ 0) hmr.ne']
    congr 1
    push_cast
    field_simp [hmr.ne']
  have hcos : cosTransform Ω (Real.log m - Real.log ((m + 2 * (r + 1) : ℕ) : ℝ)) =
      cosTransform Ω (Real.log (1 + ((2 * (r + 1) : ℕ) : ℝ) / m)) := by
    rw [show Real.log m - Real.log ((m + 2 * (r + 1) : ℕ) : ℝ) =
      -(Real.log ((m + 2 * (r + 1) : ℕ) : ℝ) - Real.log m) by ring, hphase]
    simp only [cosTransform, mul_neg, Real.cos_neg]
  have hsqrt : Real.sqrt m * Real.sqrt ((m + 2 * (r + 1) : ℕ) : ℝ) =
      Real.sqrt ((m : ℝ) * (m + ((2 * (r + 1) : ℕ) : ℝ))) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg m), Nat.cast_add]
  dsimp only [F]
  rw [hdist, hcos, hsqrt]
  simp only [Nat.cast_add]
  ring

/-- Exact decomposition of the literal ordered-pair model into positive even
rows and the endpoint variation of its actual taper. Both finite cutoffs are
retained in the row length. -/
theorem stabilizerModelOddCoalSum_eq_logarithmic_rows
    (Q : ℕ) (Ω g : ℝ → ℝ) (X θ : ℝ) :
    stabilizerModelOddCoalSum Q Ω g X θ =
      (1 / (4 * π)) * ∑ m ∈ primeRange X, if 3 ≤ m ∧ m % 2 = 1 then
        2 * g (Real.log m) * stabilizerLogarithmicRow Q Ω m
          (stabilizerApertureLength ⌊X⌋₊ θ m) +
        stabilizerTaperVariation Q Ω g m (stabilizerApertureLength ⌊X⌋₊ θ m)
      else 0 := by
  rw [model_eq_upper]
  congr 1
  apply sum_congr rfl
  intro m _
  by_cases hm : 3 ≤ m ∧ m % 2 = 1
  · rw [if_pos hm]
    exact upper_row_eq_logarithmic Q ⌊X⌋₊ m Ω g θ hm.1 hm.2
  · rw [if_neg hm]
    apply sum_eq_zero
    intro n _
    have hc : ¬ (3 ≤ m ∧ 3 ≤ n ∧ m % 2 = 1 ∧ n % 2 = 1 ∧ m ≠ n ∧
        |Real.log m - Real.log n| ≤ θ) := fun h => hm ⟨h.1, h.2.2.1⟩
    simp only [modelPairWeight, if_neg hc, zero_mul, ite_self]

private theorem model_sub_anchored_rows (Q : ℕ) (Ω g : ℝ → ℝ) (X θ : ℝ) :
    stabilizerModelOddCoalSum Q Ω g X θ -
      (1 / (2 * π)) * (∑ m ∈ primeRange X, if 3 ≤ m ∧ m % 2 = 1 then
        g (Real.log m) * stabilizerLogarithmicRow Q Ω m
          (stabilizerApertureLength ⌊X⌋₊ θ m) else 0) =
      (1 / (4 * π)) * ∑ m ∈ primeRange X, if 3 ≤ m ∧ m % 2 = 1 then
        stabilizerTaperVariation Q Ω g m (stabilizerApertureLength ⌊X⌋₊ θ m) else 0 := by
  rw [stabilizerModelOddCoalSum_eq_logarithmic_rows]
  simp only [mul_sum]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro m _
  split_ifs <;> ring

/-- Anchoring the actual taper at the smaller endpoint of each literal pair
costs at most `C floor(X) O(Q)/T` for a fixed smooth height profile. -/
theorem WindowProfile.exists_model_taper_transport_le {ε : ℝ} {u : ℝ → ℝ}
    (hu : WindowProfile ε u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ → ℝ) (L w T X θ : ℝ) (Q : ℕ),
      TaperProfile ρ → 0 < w → 2 * w ≤ L → 1 ≤ T → θ ≤ Real.log 2 →
      |stabilizerModelOddCoalSum Q (profileΩ u T) (Taper.g ρ L w) X θ -
        (1 / (2 * π)) * (∑ m ∈ primeRange X, if 3 ≤ m ∧ m % 2 = 1 then
          Taper.g ρ L w (Real.log m) * stabilizerLogarithmicRow Q (profileΩ u T) m
            (stabilizerApertureLength ⌊X⌋₊ θ m) else 0)| ≤
        (⌊X⌋₊ : ℝ) *
          (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) * C / T := by
  obtain ⟨C, hC, hCb⟩ := hu.exists_stabilizerTaperVariation_le
  refine ⟨C, hC, ?_⟩
  intro ρ L w T X θ Q hρ hw hwL hT hθ
  let O : ℝ := ∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q
  have hO : 0 ≤ O := sum_nonneg (fun q _ => RHTower.Sieve.sqfreeTotientInv_nonneg q)
  have hTr : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hterm (m : ℕ) :
      |if 3 ≤ m ∧ m % 2 = 1 then
        stabilizerTaperVariation Q (profileΩ u T) (Taper.g ρ L w) m
          (stabilizerApertureLength ⌊X⌋₊ θ m) else 0| ≤ O * C / T := by
    by_cases hm : 3 ≤ m ∧ m % 2 = 1
    · rw [if_pos hm]
      exact hCb ρ L w T m Q (stabilizerApertureLength ⌊X⌋₊ θ m) hρ hw hwL hT
        (by exact_mod_cast (by omega : 0 < m))
        (by exact_mod_cast two_mul_stabilizerApertureLength_le ⌊X⌋₊ m hθ)
    · rw [if_neg hm, abs_zero]
      positivity
  have hsum : (∑ m ∈ primeRange X,
      |if 3 ≤ m ∧ m % 2 = 1 then
        stabilizerTaperVariation Q (profileΩ u T) (Taper.g ρ L w) m
          (stabilizerApertureLength ⌊X⌋₊ θ m) else 0|) ≤ (⌊X⌋₊ : ℝ) * (O * C / T) := by
    simpa only [primeRange, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul] using
      sum_le_card_nsmul (primeRange X) _ (O * C / T) (fun m _ => hterm m)
  have hπ0 : (0 : ℝ) ≤ 1 / (4 * π) := by positivity
  have hπ1 : (1 : ℝ) / (4 * π) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < 4 * π)]
    linarith [Real.pi_gt_three]
  rw [model_sub_anchored_rows, abs_mul, abs_of_nonneg hπ0]
  calc
    _ ≤ (1 / (4 * π)) * (∑ m ∈ primeRange X,
      |if 3 ≤ m ∧ m % 2 = 1 then
        stabilizerTaperVariation Q (profileΩ u T) (Taper.g ρ L w) m
          (stabilizerApertureLength ⌊X⌋₊ θ m) else 0|) :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hπ0
    _ ≤ (1 / (4 * π)) * ((⌊X⌋₊ : ℝ) * (O * C / T)) :=
      mul_le_mul_of_nonneg_left hsum hπ0
    _ ≤ (⌊X⌋₊ : ℝ) * (O * C / T) :=
      mul_le_of_le_one_left (by positivity) hπ1
    _ = _ := by ring

end GaloisForLFunctions.TransThresholdPairCorrelation
