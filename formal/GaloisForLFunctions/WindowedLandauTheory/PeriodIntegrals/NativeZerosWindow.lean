import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.DirichletLUniformLocalCount
import GaloisForLFunctions.RHTower.XiCosineShiftDefectZeroDensity
import GaloisForLFunctions.RHTower.XiWindowZeroCount
import GaloisForLFunctions.WindowedLandauTheory.PeriodIntegrals.ZerosWindow

/-! Transfer the corpus's local multiplicity counts to the primitive zero windows. -/

open Finset RHTower DirichletCharacter Zeta23.ThmE

namespace PI

private theorem zeta_window :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      let Z := {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ riemannZeta ρ = 0}
      Z.Finite ∧ ∑ᶠ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ C * Real.log (|t| + 2) := by
  let B := |xiLineTwoLogDerivConstant| / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hB : 0 ≤ B := div_nonneg (abs_nonneg _) hlog2.le
  refine ⟨16 * (B + 2), by linarith only [hB], fun t => ?_⟩
  classical
  let Z := {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ riemannZeta ρ = 0}
  have hWin := finite_xiOrdinateWindow 1 t
  have hx : ∀ ρ ∈ Z, xi ρ = 0 := by
    intro ρ hρ
    obtain ⟨h0, h1, _, hz⟩ := hρ
    have hρ0 : ρ ≠ 0 := fun e => by rw [e, Complex.zero_re] at h0; exact (lt_irrefl _ h0)
    have hρ1 : ρ ≠ 1 := fun e => by rw [e, Complex.one_re] at h1; exact (lt_irrefl _ h1)
    rw [xi_eq_archFactor_mul_zeta hρ0 hρ1 (Complex.Gammaℝ_ne_zero_of_re_pos h0), hz, mul_zero]
  have hsub : Z ⊆ (fun q : XiZeroCopy => (q.1 : ℂ)) '' xiOrdinateWindow 1 t := by
    intro ρ hρ
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero (hx ρ hρ)
    refine ⟨q, ?_, hq⟩
    rw [mem_xiOrdinateWindow_iff, hq]
    exact hρ.2.2.1
  have hZ := (hWin.image _).subset hsub
  refine ⟨hZ, ?_⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hZ]
  have hs := sum_order_le_ncard_of_subset
    (F := hZ.toFinset) (fun w hw => hx w (hZ.mem_toFinset.mp hw)) hWin
    (fun q hq => (hZ.mem_toFinset.mp hq).2.2.1)
  have horders : (∑ ρ ∈ hZ.toFinset, analyticOrderNatAt riemannZeta ρ) =
      ∑ ρ ∈ hZ.toFinset, (analyticOrderAt xi ρ).toNat := by
    refine sum_congr rfl fun ρ hρ => ?_
    obtain ⟨h0, h1, _, _⟩ := hZ.mem_toFinset.mp hρ
    rw [analyticOrderNatAt, xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩]
  have hsum : (∑ ρ ∈ hZ.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
      (xiOrdinateWindow 1 t).ncard := by
    rw [← Nat.cast_sum, horders]
    exact_mod_cast hs
  have hlog : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith only [abs_nonneg t])
  have hshift : Real.log (|t| + 4) ≤ 2 * Real.log (|t| + 2) := by
    have hpow : |t| + 4 ≤ (|t| + 2) ^ 2 := by nlinarith only [abs_nonneg t, sq_nonneg |t|]
    have h := Real.log_le_log (by positivity : 0 < |t| + 4) hpow
    rw [Real.log_pow] at h
    simpa using h
  have hCoef : xiLineTwoLogDerivConstant ≤ B * Real.log (|t| + 2) := by
    calc xiLineTwoLogDerivConstant ≤ |xiLineTwoLogDerivConstant| := le_abs_self _
      _ = B * Real.log 2 := by dsimp [B]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog hB
  have hcount := ncard_xiOrdinateWindow_le_log 1 t
  norm_num at hcount
  exact hsum.trans (hcount.trans (by linarith only [hCoef, hshift]))

private theorem dirichlet_window :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      1 < N → χ.IsPrimitive → ∀ t : ℝ,
      (ZerosNear χ t).Finite ∧
        ∑ᶠ ρ ∈ ZerosNear χ t, (analyticOrderNatAt χ.LFunction ρ : ℝ) ≤
          C * Real.log (N * (|t| + 2)) := by
  obtain ⟨A, hA, hcount⟩ := exists_uniform_localCount
  refine ⟨9 * A, by positivity, fun N _ χ hN hp t => ?_⟩
  classical
  let Z₀ := zerosInL χ (t - 2) (t - 1)
  let Z₁ := zerosInL χ (t - 1) t
  let Z₂ := zerosInL χ t (t + 1)
  have hf (a b : ℝ) : (zerosInL χ a b).Finite := (LSeam_of hN hp).finite_window a b
  have hZ₀ : Z₀.Finite := hf _ _
  have hZ₁ : Z₁.Finite := hf _ _
  have hZ₂ : Z₂.Finite := hf _ _
  have hsub : ZerosNear χ t ⊆ Z₀ ∪ Z₁ ∪ Z₂ := by
    intro ρ hρ
    obtain ⟨h0, h1, ht, hz⟩ := hρ
    obtain ⟨hl, hu⟩ := abs_le.mp ht
    by_cases h : ρ.im ≤ t - 1
    · exact Or.inl (Or.inl ⟨⟨hz, h0, h1⟩, by linarith, h⟩)
    · by_cases h' : ρ.im ≤ t
      · exact Or.inl (Or.inr ⟨⟨hz, h0, h1⟩, lt_of_not_ge h, h'⟩)
      · exact Or.inr ⟨⟨hz, h0, h1⟩, lt_of_not_ge h', by linarith⟩
  have hZ := ((hZ₀.union hZ₁).union hZ₂).subset hsub
  refine ⟨hZ, ?_⟩
  let m (ρ : ℂ) : ℝ := (zeroMultL χ ρ : ℝ)
  have hfin : hZ.toFinset ⊆ hZ₀.toFinset ∪ hZ₁.toFinset ∪ hZ₂.toFinset := by
    intro ρ hρ
    simpa only [Finset.mem_union, Set.Finite.mem_toFinset] using hsub (hZ.mem_toFinset.mp hρ)
  have hdisj01 : Disjoint hZ₀.toFinset hZ₁.toFinset := by
    rw [Finset.disjoint_left]
    intro ρ h0 h1
    exact (lt_irrefl _ (((hZ₁.mem_toFinset.mp h1).2.1).trans_le (hZ₀.mem_toFinset.mp h0).2.2))
  have hdisj2 : Disjoint (hZ₀.toFinset ∪ hZ₁.toFinset) hZ₂.toFinset := by
    rw [Finset.disjoint_left]
    intro ρ h01 h2
    have ht : t < ρ.im := (hZ₂.mem_toFinset.mp h2).2.1
    rcases Finset.mem_union.mp h01 with h0 | h1
    · have h0' : ρ.im ≤ t - 1 := (hZ₀.mem_toFinset.mp h0).2.2
      linarith
    · exact (not_lt_of_ge (hZ₁.mem_toFinset.mp h1).2.2) ht
  have hsum (a b : ℝ) (hF : (zerosInL χ a b).Finite) :
      ∑ ρ ∈ hF.toFinset, m ρ = (NcountL χ a b : ℝ) := by
    rw [NcountL, finsum_mem_eq_finite_toFinset_sum _ hF, Nat.cast_sum]
    rfl
  have hQ : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hlog (j : ℝ) (hj : |j| ≤ 2) :
      Real.log (N * (|t - j| + 3)) ≤ 3 * Real.log (N * (|t| + 2)) := by
    have hbase : 2 ≤ (N : ℝ) * (|t| + 2) := by
      exact (by linarith only [abs_nonneg t] : 2 ≤ |t| + 2).trans
        (le_mul_of_one_le_left (by positivity) hQ)
    have habs : |t - j| + 3 ≤ 3 * (|t| + 2) := by
      have habs' : |t - j| ≤ |t| + |j| := by simpa only [Real.norm_eq_abs] using norm_sub_le t j
      linarith only [habs', hj, abs_nonneg t]
    have hs := mul_le_mul_of_nonneg_left habs (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have hcube : (N : ℝ) * (|t - j| + 3) ≤ ((N : ℝ) * (|t| + 2)) ^ 3 := by
      set b : ℝ := (N : ℝ) * (|t| + 2)
      have hsq : 3 ≤ b ^ 2 := (by norm_num : (3 : ℝ) ≤ 2 ^ 2).trans
        (pow_le_pow_left₀ (by norm_num) hbase 2)
      calc (N : ℝ) * (|t - j| + 3) ≤ (N : ℝ) * (3 * (|t| + 2)) := hs
        _ = 3 * b := by rw [b]; ring
        _ ≤ b ^ 2 * b := mul_le_mul_of_nonneg_right hsq (by positivity)
        _ = b ^ 3 := by ring
    have h := Real.log_le_log (by positivity : 0 < (N : ℝ) * (|t - j| + 3)) hcube
    rw [Real.log_pow] at h
    simpa using h
  have b₀ := hcount N χ hN hp (t - 2)
  have b₁ := hcount N χ hN hp (t - 1)
  have b₂ := hcount N χ hN hp t
  have h₀ := b₀.trans (mul_le_mul_of_nonneg_left (hlog 2 (by norm_num)) hA.le)
  have h₁ := b₁.trans (mul_le_mul_of_nonneg_left (hlog 1 (by norm_num)) hA.le)
  have h₂ := b₂.trans (mul_le_mul_of_nonneg_left (by simpa using hlog 0 (by norm_num)) hA.le)
  have e₀ : t - 2 + 1 = t - 1 := by ring
  rw [e₀] at h₀
  have e₁ : t - 1 + 1 = t := by ring
  rw [e₁] at h₁
  rw [finsum_mem_eq_finite_toFinset_sum _ hZ]
  change ∑ ρ ∈ hZ.toFinset, m ρ ≤ _
  calc ∑ ρ ∈ hZ.toFinset, m ρ ≤ ∑ ρ ∈ hZ₀.toFinset ∪ hZ₁.toFinset ∪ hZ₂.toFinset, m ρ :=
        Finset.sum_le_sum_of_subset_of_nonneg hfin (fun _ _ _ => Nat.cast_nonneg _)
    _ = (NcountL χ (t - 2) (t - 1) : ℝ) + NcountL χ (t - 1) t + NcountL χ t (t + 1) := by
      rw [Finset.sum_union hdisj2, Finset.sum_union hdisj01, hsum, hsum, hsum]
    _ ≤ _ := by linarith only [h₀, h₁, h₂]

theorem zerosWindow_closed : ZerosWindow := by
  obtain ⟨C₀, hC₀, hζ⟩ := zeta_window
  obtain ⟨C₁, hC₁, hL⟩ := dirichlet_window
  refine ⟨max C₀ C₁, hC₀.trans_le (le_max_left _ _), ?_⟩
  intro N _ χ hp t
  by_cases hN : N = 1
  · subst N
    simp only [ZerosNear, LFunction_modOne_eq, Nat.cast_one, one_mul]
    obtain ⟨hf, h⟩ := hζ t
    exact ⟨hf, h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.log_nonneg (by linarith only [abs_nonneg t])))⟩
  · have hN' : 1 < N := lt_of_le_of_ne (NeZero.pos N) hN.symm
    obtain ⟨hf, h⟩ := hL N χ hN' hp t
    have hlog : 0 ≤ Real.log (N * (|t| + 2)) := by
      apply Real.log_nonneg
      exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast NeZero.pos N)
        (by linarith only [abs_nonneg t])
    exact ⟨hf, h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog)⟩

end PI
