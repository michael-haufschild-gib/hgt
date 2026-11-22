import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.WeightedZeroPackets
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroRepulsion.SharpRepulsion
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ConductorHeightLogarithms
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ChebyshevStatement
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroChangeLevel

/-! Log-free density and exceptional-zero repulsion give relative decay at polynomial scale. -/

open Finset Complex WindowedLandauTheory.ZeroFreeDirichlet
open scoped Classical

noncomputable section

namespace QH.PrimeProgressions

private theorem exceptional_gap_scale {M : ℕ} [NeZero M] (hM : 8 ≤ M)
    (ℓ F c₁ c₂ : ℝ) (hℓ : 0 < ℓ) (hF : 1 ≤ F) (hℓM : ℓ ≤ F * Real.log M)
    (hc₁ : 0 < c₁)
    (Z : DirichletCharacter ℂ M → Finset ℂ)
    (hgap : ∀ χ, ∀ ρ ∈ Z χ, cZ ≤ ℓ * (1 - ρ.re))
    (hrep : ∀ (χ₁ : DirichletCharacter ℂ M) (β : ℝ), eOf M = some (χ₁, β) →
      InRegion cZ M (β : ℂ) → 1 - c₁ / ℓ < β →
      ∀ χ, ∀ ρ ∈ Z χ, c₂ * Real.log (c₁ / ((1 - β) * ℓ)) ≤ ℓ * (1 - ρ.re)) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ etaOf M / min 1 (min (cZ / 2) (c₁ / F)) ∧ θ ≤ 1 ∧
      ∀ χ, ∀ ρ ∈ Z χ, (cZ + c₂ * Real.log (1 / θ)) / 2 ≤ ℓ * (1 - ρ.re) := by
  let η₀ := min 1 (min (cZ / 2) (c₁ / F))
  have hF₀ : 0 < F := zero_lt_one.trans_le hF
  have hη : 0 < η₀ :=
    lt_min one_pos (lt_min (div_pos cZ_pos (by norm_num)) (div_pos hc₁ hF₀))
  have hη₁ : η₀ ≤ 1 := min_le_left _ _
  have hηZ : η₀ ≤ cZ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηc : η₀ ≤ c₁ / F := (min_le_right _ _).trans (min_le_right _ _)
  by_cases hlarge : η₀ ≤ etaOf M
  · refine ⟨1, one_pos, (le_div_iff₀ hη).mpr (by simpa using hlarge), le_rfl, ?_⟩
    intro χ ρ hρ
    simp only [div_one, Real.log_one, mul_zero, add_zero]
    linarith only [hgap χ ρ hρ, cZ_pos]
  have hsmall : etaOf M < η₀ := lt_of_not_ge hlarge
  rcases he : eOf M with _ | ⟨χ₁, β⟩
  · rw [etaOf_none M he] at hsmall
    exact (not_lt_of_ge hη₁ hsmall).elim
  have hβ : β < 1 := (eOf_exc M (χ₁, β) he).2.2.2.2
  have hβ₀ : 0 < 1 - β := sub_pos.mpr hβ
  have hregion : InRegion cZ M (β : ℂ) := by
    by_contra h
    exact (not_le_of_gt (hsmall.trans_le hηZ)) (etaOf_far M (by omega) χ₁ β he h)
  have hηeq : etaOf M = (1 - β) * Real.log M := by
    rw [etaOf_some M χ₁ β he] at hsmall ⊢
    rcases min_choice (1 : ℝ) ((1 - β) * Real.log M) with h | h
    · rw [h] at hsmall
      exact (not_lt_of_ge hη₁ hsmall).elim
    · exact h
  have hprod : (1 - β) * ℓ < c₁ := by
    have ht : etaOf M * F < c₁ := by
      have h := (mul_lt_mul_of_pos_right (hsmall.trans_le hηc) hF₀)
      rwa [div_mul_cancel₀ _ hF₀.ne'] at h
    rw [hηeq] at ht
    calc
      (1 - β) * ℓ ≤ (1 - β) * (F * Real.log M) := mul_le_mul_of_nonneg_left hℓM hβ₀.le
      _ = (1 - β) * Real.log M * F := by ring
      _ < _ := ht
  let θ := (1 - β) * ℓ / c₁
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have hθ₁ : θ ≤ 1 := (div_le_one hc₁).mpr hprod.le
  have hθe : θ ≤ etaOf M / η₀ := by
    apply (le_div_iff₀ hη).mpr
    calc
      θ * η₀ ≤ θ * (c₁ / F) := mul_le_mul_of_nonneg_left hηc hθ.le
      _ = (1 - β) * (ℓ / F) := by dsimp only [θ]; field_simp [hc₁.ne', hF₀.ne']
      _ ≤ _ := by rw [hηeq]; exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hF₀).mpr
        (by simpa only [mul_comm F] using hℓM)) hβ₀.le
  refine ⟨θ, hθ, hθe, hθ₁, fun χ ρ hρ => ?_⟩
  have ht : 1 - c₁ / ℓ < β := by
    have h : 1 - β < c₁ / ℓ := (lt_div_iff₀ hℓ).mpr hprod
    linarith only [h]
  have hd := hrep χ₁ β he hregion ht χ ρ hρ
  have heq : 1 / θ = c₁ / ((1 - β) * ℓ) := by dsimp only [θ]; rw [one_div_div]
  rw [heq]
  linarith only [hgap χ ρ hρ, hd]

theorem polynomial_zero_sum :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 20 ∧ ∀ F : ℝ, 1 ≤ F → ∃ c A C : ℝ, 0 < c ∧ 0 < A ∧ 0 < C ∧
      ∀ (M : ℕ) [NeZero M] (Z : DirichletCharacter ℂ M → Finset ℂ)
        (m : DirichletCharacter ℂ M → ℂ → ℕ), 8 ≤ M →
        (∀ χ, ∀ ρ ∈ Z χ, IsLZero χ ρ ∧ 1 - κ < ρ.re ∧ |ρ.im| ≤ (M : ℝ) ^ F + 1) →
        (∀ χ, ∀ ρ ∈ Z χ, m χ ρ = analyticOrderNatAt χ.LFunction ρ) →
        ∀ y : ℝ, 2 ≤ y → C * Real.log M ≤ Real.log y →
        ∑ χ : DirichletCharacter ℂ M, ∑ ρ ∈ Z χ,
          ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1) ≤
          A * etaOf M * Real.exp (-(c * Real.log y / Real.log M)) := by
  obtain ⟨D, B, κ₁, hD, hB, hκ₁, hdensity⟩ := weighted_zero_packets
  obtain ⟨κ₂, c₁, c₂, hκ₂, hc₁, hc₂, hrep⟩ := deuring_heilbronn_sharp
  let κ : ℝ := min (1 / 20) (min κ₁ κ₂)
  have hκ : 0 < κ := lt_min (by norm_num) (lt_min hκ₁ hκ₂)
  have hκ1 : κ ≤ κ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hκ2 : κ ≤ κ₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hcZ := cZ_pos
  refine ⟨κ, hκ, min_le_left _ _, ?_⟩
  intro F hF
  let H := F + 2
  have hH : 1 ≤ H := by dsimp only [H]; linarith only [hF]
  have hH₀ : 0 < H := zero_lt_one.trans_le hH
  let η₀ := min 1 (min (cZ / 2) (c₁ / H))
  have hη₀ : 0 < η₀ := lt_min one_pos (lt_min (by positivity) (div_pos hc₁ hH₀))
  let c := cZ / (4 * H)
  have hc : 0 < c := by dsimp only [c]; positivity
  refine ⟨c, B / η₀, H * max D (4 / c₂), hc, by positivity, by positivity, ?_⟩
  intro M _ Z m hM hZ hm y hy hY
  let T := (M : ℝ) ^ F + 3
  let ℓ := Real.log ((M : ℝ) * T)
  obtain ⟨hMlog, hℓlo, hℓhi⟩ := ell_bounds M hM F hF
  have hℓ : 0 < ℓ := by linarith only [hMlog, hℓlo]
  have hT : 2 ≤ T := by
    have hp : 0 ≤ (M : ℝ) ^ F := by positivity
    dsimp only [T]
    linarith only [hp]
  have hY₀ : 0 < Real.log y := Real.log_pos (by linarith only [hy])
  have hℓy : max D (4 / c₂) * ℓ ≤ Real.log y := by
    calc
      max D (4 / c₂) * ℓ ≤ max D (4 / c₂) * (H * Real.log M) :=
        mul_le_mul_of_nonneg_left hℓhi (by positivity)
      _ = H * max D (4 / c₂) * Real.log M := by ring
      _ ≤ _ := hY
  let w (χ : DirichletCharacter ℂ M) (ρ : ℂ) := (m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)
  let V (χ : DirichletCharacter ℂ M) := (Z χ).filter (fun ρ => 0 < w χ ρ)
  have hnoreg (χ : DirichletCharacter ℂ M) (ρ : ℂ) (hρ : ρ ∈ V χ) :
      ¬ InRegion cZ M ρ := by
    intro hr
    obtain ⟨hmem, hw⟩ := mem_filter.mp hρ
    have hz := (hZ χ ρ hmem).1
    obtain ⟨β, he, hρβ, hd⟩ := zero_in_region M (by omega) χ ρ hr hz
    have horder := (lFunction_analyticAt χ hz.1).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz.2 hd
    have hm₁ : m χ ρ = 1 := by simp [hm χ ρ hmem, analyticOrderNatAt, horder]
    change 0 < (m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ) at hw
    rw [hm₁] at hw
    simp [excW, he, hρβ] at hw
  have hgap (χ : DirichletCharacter ℂ M) (ρ : ℂ) (hρ : ρ ∈ V χ) : cZ ≤ ℓ * (1 - ρ.re) := by
    have hmem := (mem_filter.mp hρ).1
    have ht : |ρ.im| + 2 ≤ T := by linarith only [(hZ χ ρ hmem).2.2]
    have hf : 0 < Real.log ((M : ℝ) * (|ρ.im| + 2)) := by
      have hM' : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
      exact Real.log_pos ((show (1 : ℝ) < |ρ.im| + 2 by linarith [abs_nonneg ρ.im]).trans_le
        (le_mul_of_one_le_left (by positivity) hM'))
    have hL := Real.log_le_log (show 0 < (M : ℝ) * (|ρ.im| + 2) by positivity)
      (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg M))
    have hn := hnoreg χ ρ hρ
    unfold InRegion at hn
    have h₀ := (div_lt_iff₀ hf).mp (show cZ / Real.log ((M : ℝ) * (|ρ.im| + 2)) < 1 - ρ.re by
      linarith only [lt_of_not_ge hn])
    have hr : 0 ≤ 1 - ρ.re := sub_nonneg.mpr (re_lt_one_of_isLZero (hZ χ ρ hmem).1).le
    exact h₀.le.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hL hr)
  obtain ⟨θ, hθ, hθe, hθ₁, hg⟩ := exceptional_gap_scale hM ℓ H c₁ c₂ hℓ hH hℓhi
    hc₁ V hgap (by
      intro χ₁ β he hreg hβnear χ ρ hρ
      have hmem := (mem_filter.mp hρ).1
      obtain ⟨hz, hre, him⟩ := hZ χ ρ hmem
      obtain ⟨hsq, hne, hzero, -, hβ⟩ := eOf_exc M (χ₁, β) he
      have hpair : (χ, ρ) ≠ (χ₁, (β : ℂ)) := by
        intro e
        exact hnoreg χ ρ hρ ((Prod.mk.inj e).2.symm ▸ hreg)
      have h := hrep M χ₁ χ β T ρ (by omega) hT hsq hne hzero hβnear hβ hz
        (by linarith only [hre, hκ2]) (by linarith only [him]) hpair
      exact ((div_le_iff₀ hℓ).mp h).trans_eq (mul_comm _ _))
  have hlogθ : 0 ≤ Real.log (1 / θ) :=
    Real.log_nonneg ((le_div_iff₀ hθ).mpr (by simpa using hθ₁))
  let η := (cZ + c₂ * Real.log (1 / θ)) / 2 / ℓ
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  have hsum := hdensity M T y η V hT (by linarith only [hy])
    ((mul_le_mul_of_nonneg_right (le_max_left _ _) hℓ.le).trans hℓy) hη (by
      intro χ ρ hρ
      obtain ⟨hz, hre, him⟩ := hZ χ ρ (mem_filter.mp hρ).1
      have hg' := (div_le_iff₀ hℓ).mpr (by simpa only [mul_comm] using hg χ ρ hρ)
      exact ⟨by linarith only [hκ1, hre], by linarith only [hg'], by linarith only [him], hz⟩)
  have hfactor : y ^ (-η / 2) ≤ θ * Real.exp (-(c * Real.log y / Real.log M)) := by
    have hterm := (mul_le_mul_of_nonneg_right (le_max_right D (4 / c₂)) hℓ.le).trans hℓy
    have hθlog : Real.log (1 / θ) = -Real.log θ := by rw [one_div, Real.log_inv]
    have hpay : Real.log (1 / θ) ≤ (c₂ * Real.log y / (4 * ℓ)) * Real.log (1 / θ) := by
      refine le_mul_of_one_le_left hlogθ ?_
      rw [le_div_iff₀ (by positivity), one_mul]
      calc 4 * ℓ = c₂ * (4 / c₂ * ℓ) := by field_simp [hc₂.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left hterm hc₂.le
    have hdecay : c * Real.log y / Real.log M ≤ cZ * Real.log y / (4 * ℓ) := by
      have hM₀ : 0 < Real.log M := by linarith only [hMlog]
      have he : c * Real.log y / Real.log M = cZ * Real.log y / (4 * (H * Real.log M)) := by
        dsimp only [c]
        field_simp [hH₀.ne', hM₀.ne']
      rw [he]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hℓhi (by norm_num))
    rw [Real.rpow_def_of_pos (by linarith only [hy]), ← Real.exp_log hθ, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he : Real.log y * (-η / 2) =
        -(cZ * Real.log y / (4 * ℓ)) - (c₂ * Real.log y / (4 * ℓ)) * Real.log (1 / θ) := by
      dsimp only [η]
      field_simp [hℓ.ne']
      ring
    rw [he]
    linarith only [hpay, hdecay, hθlog]
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ M, ∑ ρ ∈ V χ,
        (analyticOrderNatAt χ.LFunction ρ : ℝ) * y ^ (ρ.re - 1) := by
      refine sum_le_sum fun χ _ => ?_
      dsimp only [V]
      rw [sum_filter]
      refine sum_le_sum fun ρ hρ => ?_
      have hp : 0 ≤ y ^ (ρ.re - 1) := by positivity
      split_ifs with h
      · rw [← hm χ ρ hρ]
        exact mul_le_mul_of_nonneg_right (sub_le_self _ (Nat.cast_nonneg _)) hp
      · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hp
    _ ≤ B * y ^ (-η / 2) := hsum
    _ ≤ B * (θ * Real.exp (-(c * Real.log y / Real.log M))) :=
      mul_le_mul_of_nonneg_left hfactor hB.le
    _ ≤ _ := by
      rw [show B / η₀ * etaOf M = B * (etaOf M / η₀) by ring]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hθe (Real.exp_pos _).le) hB.le

end QH.PrimeProgressions
