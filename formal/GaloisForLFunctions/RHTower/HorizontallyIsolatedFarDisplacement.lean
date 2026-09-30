import GaloisForLFunctions.RHTower.HorizontallyIsolatedSimpleZeros
import GaloisForLFunctions.RHTower.SelbergExponentialNearLineDensity
import GaloisForLFunctions.RHTower.ZetaLineLogMeanLittlewoodBudget

/-!
# Horizontal isolation at every displacement beyond the critical scale

A simple critical zero `ρ = ½ + iγ` is horizontally isolated at scale `δ` if no off-line zero with
ordinate `γ` lies within horizontal distance `δ` of the line (`ZetaHorizIsolated`). Here the far
side is added: `ZetaHorizIsolatedFar Δ ρ` says every off-line zero with ordinate `γ` lies within
distance `Δ` of the line.

The critical zeros that are isolated at scale `δ` but not far-isolated at `Δ` inject into the zeros
`ρ'` with `T < Im ρ' ≤ 2T` and `|Re ρ' − ½| ≥ Δ` (two critical zeros with the same ordinate
coincide), and by the reflection `ρ ↦ 1 − ρ̄` those are at most twice the zeros with
`Re ρ − ½ ≥ Δ`. With `Δ = 2a/log(4T)` the exponential near-line density
(`exists_selberg_exponential_nearLine_zeroDensity` at `U = 4T`) and the local zero count bound this by
`B (T log(4T) e^{−a/1200}/a + log²(4T))`. Hence (`exists_horizontallyIsolated_band_le`): for every
`ε > 0` there is `B` such that for all large `T` and every `1 ≤ a` with `2a + 2 ≤ log(4T)`,

`(HD(1) − ε)·N(T, 2T) − B (T log(4T) e^{−a/1200}/a + log²(4T))`

simple critical zeros with `T < γ ≤ 2T` have every same-ordinate off-line zero at horizontal distance
in `(5/(2 log(T/2π)), 2a/log(4T))` from the line.
-/

open Complex Set Filter
open Zeta23 Zeta23.ThmD

namespace RHTower

noncomputable section

/-- Every off-line zero with the ordinate of `ρ` lies within horizontal distance `Δ` of the line. -/
def ZetaHorizIsolatedFar (Δ : ℝ) (ρ : ℂ) : Prop :=
  ∀ ρ' : ℂ, IsNontrivialZero ρ' → ρ'.im = ρ.im → ρ'.re ≠ 1 / 2 → |ρ'.re - 1 / 2| < Δ

/-- Simple critical zeros with `T₁ < γ ≤ T₂`, isolated at scale `δ` and far-isolated at `Δ`. -/
def N0simpleIsolatedBand (δ Δ T₁ T₂ : ℝ) : ℕ :=
  (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | Zeta23.zeroMult ρ = 1} ∩ {ρ | ZetaHorizIsolated δ ρ} ∩
    {ρ | ZetaHorizIsolatedFar Δ ρ}).ncard

/-- The zeros with `T₁ < γ ≤ T₂` at horizontal distance at least `Δ` from the line. -/
def farZeros (Δ T₁ T₂ : ℝ) : Set ℂ := {ρ | ρ ∈ zerosIn T₁ T₂ ∧ Δ ≤ |ρ.re - 1 / 2|}

theorem farZeros_finite (Δ T₁ T₂ : ℝ) : (farZeros Δ T₁ T₂).Finite :=
  (zerosIn_finite T₁ T₂).subset fun _ h => h.1

/-- **The failing critical zeros inject into the far zeros.** -/
theorem N0simpleIsolated_le_band_add_far (δ Δ T₁ T₂ : ℝ) :
    N0simpleIsolated δ T₁ T₂ ≤ N0simpleIsolatedBand δ Δ T₁ T₂ + (farZeros Δ T₁ T₂).ncard := by
  classical
  set A := zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | Zeta23.zeroMult ρ = 1} ∩
    {ρ | ZetaHorizIsolated δ ρ} with hA
  set B := A ∩ {ρ | ZetaHorizIsolatedFar Δ ρ} with hB
  have hAfin : A.Finite := (zerosIn_finite T₁ T₂).subset fun _ h => h.1.1.1
  have hsplit : A ⊆ B ∪ (A \ B) := fun x hx => by
    by_cases h : x ∈ B
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩
  have hdiff : (A \ B).ncard ≤ (farZeros Δ T₁ T₂).ncard := by
    have hpick : ∀ ρ ∈ A \ B, ∃ ρ', IsNontrivialZero ρ' ∧ ρ'.im = ρ.im ∧ ρ'.re ≠ 1 / 2 ∧
        Δ ≤ |ρ'.re - 1 / 2| := by
      intro ρ hρ
      have hnot : ¬ ZetaHorizIsolatedFar Δ ρ := fun h => hρ.2 ⟨hρ.1, h⟩
      unfold ZetaHorizIsolatedFar at hnot
      push Not at hnot
      obtain ⟨ρ', h1, h2, h3, h4⟩ := hnot
      exact ⟨ρ', h1, h2, h3, h4⟩
    choose! f hf using hpick
    refine Set.ncard_le_ncard_of_injOn f (fun ρ hρ => ?_) (fun ρ₁ h₁ ρ₂ h₂ he => ?_)
      (farZeros_finite Δ T₁ T₂)
    · obtain ⟨hz, him, -, hΔ⟩ := hf ρ hρ
      obtain ⟨⟨⟨hw, -⟩, -⟩, -⟩ := hρ.1
      exact ⟨⟨hz, by rw [him]; exact hw.2.1, by rw [him]; exact hw.2.2⟩, hΔ⟩
    · have hi1 := (hf ρ₁ h₁).2.1
      have hi2 := (hf ρ₂ h₂).2.1
      rw [he] at hi1
      have hre1 : ρ₁.re = 1 / 2 := h₁.1.1.1.2
      have hre2 : ρ₂.re = 1 / 2 := h₂.1.1.1.2
      exact Complex.ext (by rw [hre1, hre2]) (by rw [← hi1, hi2])
  calc N0simpleIsolated δ T₁ T₂ = A.ncard := rfl
    _ ≤ (B ∪ (A \ B)).ncard := Set.ncard_le_ncard hsplit ((hAfin.subset fun _ h => h.1).union
        (hAfin.subset fun _ h => h.1))
    _ ≤ B.ncard + (A \ B).ncard := Set.ncard_union_le _ _
    _ ≤ N0simpleIsolatedBand δ Δ T₁ T₂ + (farZeros Δ T₁ T₂).ncard :=
        add_le_add (le_of_eq rfl) hdiff

/-- The zeros with `T₁ < γ ≤ T₂` and `Re ρ ≥ ½ + Δ`. -/
def rightFarZeros (Δ T₁ T₂ : ℝ) : Set ℂ := {ρ | ρ ∈ zerosIn T₁ T₂ ∧ 1 / 2 + Δ ≤ ρ.re}

theorem zetaZeroConfig_window_eq (T₁ T₂ : ℝ) : zetaZeroConfig.window T₁ T₂ = zerosIn T₁ T₂ :=
  zetaZeros_window zetaSeam T₁ T₂

theorem ncard_zerosIn_le_Ncount (T₁ T₂ : ℝ) : (zerosIn T₁ T₂).ncard ≤ Ncount T₁ T₂ := by
  have h := zetaZeroConfig.ncard_le_finsum_mult T₁ T₂ (s := zetaZeroConfig.window T₁ T₂) le_rfl
  rw [zetaZeroConfig_window_eq] at h
  have hN : zetaZeroConfig.N T₁ T₂ = Ncount T₁ T₂ := zetaZeroConfig_N T₁ T₂
  have hN' : zetaZeroConfig.N T₁ T₂ = ∑ᶠ ρ ∈ zetaZeroConfig.window T₁ T₂, zetaZeroConfig.mult ρ :=
    rfl
  rw [zetaZeroConfig_window_eq] at hN'
  omega

/-- **Reflection.** The far zeros are at most twice the right far zeros. -/
theorem ncard_farZeros_le (Δ T₁ T₂ : ℝ) :
    (farZeros Δ T₁ T₂).ncard ≤ 2 * (rightFarZeros Δ T₁ T₂).ncard := by
  have hRfin : (rightFarZeros Δ T₁ T₂).Finite := (zerosIn_finite T₁ T₂).subset fun _ h => h.1
  have hsub : farZeros Δ T₁ T₂ ⊆ rightFarZeros Δ T₁ T₂ ∪ reflect '' rightFarZeros Δ T₁ T₂ := by
    rintro ρ ⟨hρ, hΔ⟩
    rcases le_or_gt (1 / 2) ρ.re with hre | hre
    · left
      refine ⟨hρ, ?_⟩
      rw [abs_of_nonneg (by linarith)] at hΔ
      linarith
    · right
      have hmem : reflect ρ ∈ zerosIn T₁ T₂ := by
        have := zetaZeroConfig.reflect_mem_window T₁ T₂ (by rw [zetaZeroConfig_window_eq]; exact hρ)
        rwa [zetaZeroConfig_window_eq] at this
      refine ⟨reflect ρ, ⟨hmem, ?_⟩, reflect_reflect ρ⟩
      rw [reflect_re]
      rw [abs_of_neg (by linarith)] at hΔ
      linarith
  calc (farZeros Δ T₁ T₂).ncard
      ≤ (rightFarZeros Δ T₁ T₂ ∪ reflect '' rightFarZeros Δ T₁ T₂).ncard :=
        Set.ncard_le_ncard hsub (hRfin.union (hRfin.image _))
    _ ≤ (rightFarZeros Δ T₁ T₂).ncard + (reflect '' rightFarZeros Δ T₁ T₂).ncard :=
        Set.ncard_union_le _ _
    _ ≤ (rightFarZeros Δ T₁ T₂).ncard + (rightFarZeros Δ T₁ T₂).ncard :=
        add_le_add le_rfl (Set.ncard_image_le hRfin)
    _ = 2 * (rightFarZeros Δ T₁ T₂).ncard := by ring

/-- The right far zeros split into the two end strips and the closed middle window. -/
theorem ncard_rightFarZeros_le {Δ T T₁' T₂' : ℝ} (hΔ : 0 ≤ Δ) (h2 : T₁' ≤ T₂')
    {Z : Finset ℂ}
    (hZ : ∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁' T₂') ∧ riemannZeta z = 0) :
    ((rightFarZeros Δ T (2 * T)).ncard : ℝ) ≤ Ncount T T₁' + Ncount T₂' (2 * T) +
      ∑ w ∈ Z.filter (fun w => 1 / 2 + Δ ≤ w.re), ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
  classical
  set M : Set ℂ := {ρ | ρ ∈ rightFarZeros Δ T (2 * T) ∧ T₁' ≤ ρ.im ∧ ρ.im ≤ T₂'} with hM
  have hsub : rightFarZeros Δ T (2 * T) ⊆ zerosIn T T₁' ∪ M ∪ zerosIn T₂' (2 * T) := by
    rintro ρ hρ
    obtain ⟨⟨hz, hlo, hhi⟩, hre⟩ := hρ
    by_cases ha : ρ.im ≤ T₁'
    · by_cases hb : T₁' ≤ ρ.im
      · exact Or.inl (Or.inr ⟨⟨⟨hz, hlo, hhi⟩, hre⟩, hb, by linarith⟩)
      · exact Or.inl (Or.inl ⟨hz, hlo, ha⟩)
    · push Not at ha
      by_cases hc : ρ.im ≤ T₂'
      · exact Or.inl (Or.inr ⟨⟨⟨hz, hlo, hhi⟩, hre⟩, ha.le, hc⟩)
      · push Not at hc
        exact Or.inr ⟨hz, hc, hhi⟩
  have hMsub : M ⊆ ↑(Z.filter (fun w => 1 / 2 + Δ ≤ w.re)) := by
    rintro ρ ⟨⟨⟨hz, -, -⟩, hre⟩, hlo, hhi⟩
    rw [Finset.coe_filter]
    refine ⟨(hZ ρ).2 ⟨?_, hz.1⟩, hre⟩
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · rw [uIcc_of_le (by norm_num)]; exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
    · rw [uIcc_of_le h2]; exact ⟨hlo, hhi⟩
  have hMcard : (M.ncard : ℝ) ≤ ∑ w ∈ Z.filter (fun w => 1 / 2 + Δ ≤ w.re),
      ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    have h := Set.ncard_le_ncard hMsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h
    refine (Nat.cast_le.mpr h).trans ?_
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    have hwZ := (Finset.mem_filter.mp hw).1
    obtain ⟨hwbox, hw0⟩ := (hZ w).mp hwZ
    have hre := (Complex.mem_reProdIm.mp hwbox).1
    rw [uIcc_of_le (by norm_num)] at hre
    have hre1 : w.re < 1 := by
      by_contra hge
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hw0
    have hcar : w ∈ zetaZeroConfig.carrier := by
      rw [zetaZeroConfig_carrier]
      exact ⟨hw0, by linarith [hre.1], hre1⟩
    have h1 := zetaZeroConfig.one_le_mult w hcar
    rw [zetaZeroConfig_mult] at h1
    exact_mod_cast h1
  have hfin1 := zerosIn_finite T T₁'
  have hfin2 := zerosIn_finite T₂' (2 * T)
  have hMfin : M.Finite := (Finset.finite_toSet _).subset hMsub
  have hc := Set.ncard_le_ncard hsub ((hfin1.union hMfin).union hfin2)
  have hu1 := Set.ncard_union_le (zerosIn T T₁' ∪ M) (zerosIn T₂' (2 * T))
  have hu2 := Set.ncard_union_le (zerosIn T T₁') M
  have hz1 := ncard_zerosIn_le_Ncount T T₁'
  have hz2 := ncard_zerosIn_le_Ncount T₂' (2 * T)
  have : ((rightFarZeros Δ T (2 * T)).ncard : ℝ) ≤
      ((zerosIn T T₁').ncard : ℝ) + (M.ncard : ℝ) + ((zerosIn T₂' (2 * T)).ncard : ℝ) := by
    exact_mod_cast hc.trans (hu1.trans (Nat.add_le_add_right hu2 _))
  have hz1' : ((zerosIn T T₁').ncard : ℝ) ≤ Ncount T T₁' := by exact_mod_cast hz1
  have hz2' : ((zerosIn T₂' (2 * T)).ncard : ℝ) ≤ Ncount T₂' (2 * T) := by exact_mod_cast hz2
  linarith

theorem Ncount_mono_right {a b c : ℝ} (hbc : b ≤ c) : Ncount a b ≤ Ncount a c := by
  have hN : ∀ x y : ℝ, Ncount x y = ∑ᶠ ρ ∈ zetaZeroConfig.window x y, zetaZeroConfig.mult ρ := by
    intro x y
    rw [← zetaZeroConfig_N]; rfl
  rw [hN, hN]
  refine zetaZeroConfig.finsum_mult_mono a c ?_ le_rfl
  rw [zetaZeroConfig_window_eq, zetaZeroConfig_window_eq]
  rintro ρ ⟨hz, h1, h2⟩
  exact ⟨hz, h1, le_trans h2 hbc⟩

/-- The arithmetic of the band deficit. -/
theorem band_deficit_arith {A K A₀ L T a E S N₁ N₂ R : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) (hA₀ : 0 ≤ A₀)
    (hL1 : 1 ≤ L) (ha1 : 1 ≤ a) (hT : 0 ≤ T) (hE : 0 ≤ E) (hR : R ≤ N₁ + N₂ + S)
    (hN₁ : N₁ ≤ A₀ * L) (hN₂ : N₂ ≤ A₀ * L)
    (hS : S ≤ L * (T * (A * E) + K * L) / (2 * Real.pi * a)) :
    2 * R ≤ (A / Real.pi + K / Real.pi + 4 * A₀) * (T * L * E / a + L ^ 2) := by
  have hπ := Real.pi_pos
  have ha0 : 0 < a := by linarith
  set X := T * L * E / a with hX
  have hL0 : 0 ≤ L := by linarith
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have h1 : 2 * (L * (T * (A * E) + K * L) / (2 * Real.pi * a)) =
      A / Real.pi * X + K / Real.pi * (L ^ 2 / a) := by
    rw [hX]; field_simp
  have h2 : K / Real.pi * (L ^ 2 / a) ≤ K / Real.pi * L ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact div_le_self (by positivity) ha1
  have hLL : L ≤ L ^ 2 := by nlinarith
  have h3 : 4 * A₀ * L ≤ 4 * A₀ * L ^ 2 := mul_le_mul_of_nonneg_left hLL (by linarith)
  have p1 : 0 ≤ A / Real.pi * L ^ 2 := by positivity
  have p2 : 0 ≤ K / Real.pi * X := by positivity
  have p3 : 0 ≤ 4 * A₀ * X := by positivity
  have e : (A / Real.pi + K / Real.pi + 4 * A₀) * (X + L ^ 2) =
      A / Real.pi * X + A / Real.pi * L ^ 2 + K / Real.pi * X + K / Real.pi * L ^ 2 +
        4 * A₀ * X + 4 * A₀ * L ^ 2 := by ring
  rw [e]
  linarith

/-- **Horizontal isolation at every displacement beyond the critical scale.** -/
theorem exists_horizontallyIsolated_band_le :
    ∀ ε > 0, ∃ B : ℝ, 0 < B ∧ ∀ᶠ T in atTop, ∀ a : ℝ, 1 ≤ a → 2 * a + 2 ≤ Real.log (4 * T) →
      (HD 1 - ε) * (Ncount T (2 * T) : ℝ) -
          B * (T * Real.log (4 * T) * Real.exp (-(a / 1200)) / a + Real.log (4 * T) ^ 2) ≤
        N0simpleIsolatedBand (5 / (2 * l T)) (2 * a / Real.log (4 * T)) T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := horizontallyIsolated_simple_critical ε hε
  obtain ⟨A, K, hA, hK, hdens⟩ := exists_selberg_exponential_nearLine_zeroDensity
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zeta_local_zero_count
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hdens
  refine ⟨A / Real.pi + K / Real.pi + 4 * A₀, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max (max T₀ (U₀ / 4)) 20)] with T hT a ha1 ha2
  have hTT₀ : T₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTU : U₀ ≤ 4 * T := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT; linarith
  have hT8 : 20 ≤ T := le_trans (le_max_right _ _) hT
  have hiso := hT₀ T hTT₀
  obtain ⟨T₁', hT₁', T₂', hT₂', hcount⟩ := hU₀ (4 * T) hTU
  set L := Real.log (4 * T) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
  have ha0 : 0 < a := by linarith
  have hΔ : 0 ≤ 2 * a / L := by positivity
  have h4T : 4 * T / 4 = T := by ring
  have hT₁lo : T < T₁' := by have := hT₁'.1; rwa [h4T] at this
  have hT₁hi : T₁' < T + 1 := by have := hT₁'.2; rwa [h4T] at this
  have hT₂lo : 2 * T - 1 < T₂' := by have := hT₂'.1; linarith
  have hT₂hi : T₂' < 2 * T := by have := hT₂'.2; linarith
  have hT12 : T₁' < T₂' := by linarith
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset (show 20 ≤ T₁' by linarith) hT12
  have hc := hcount a ha1 ha2 Z hZ
  set S := ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * a / L ≤ w.re),
    ((analyticOrderAt riemannZeta w).toNat : ℝ) with hS
  have hSle : S ≤ L * (T * (A * Real.exp (-(a / 1200))) + K * L) / (2 * Real.pi * a) := by
    rw [le_div_iff₀ (by positivity)]
    have hlen : (T₂' - T₁') * (A * Real.exp (-(a / 1200))) ≤ T * (A * Real.exp (-(a / 1200))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e : S * (2 * Real.pi * a) = L * (2 * Real.pi * ((a / L) * S)) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (hc.trans (by linarith)) (by linarith)
  have hright := ncard_rightFarZeros_le (T := T) hΔ hT12.le hZ
  have hend1 : (Ncount T T₁' : ℝ) ≤ A₀ * Real.log (|T| + 3) :=
    (by exact_mod_cast Ncount_mono_right hT₁hi.le : (Ncount T T₁' : ℝ) ≤ Ncount T (T + 1)).trans
      (hloc T)
  have hend2 : (Ncount T₂' (2 * T) : ℝ) ≤ A₀ * Real.log (|T₂'| + 3) := by
    have : (Ncount T₂' (2 * T) : ℝ) ≤ Ncount T₂' (T₂' + 1) := by
      exact_mod_cast Ncount_mono_right (by linarith)
    exact this.trans (hloc T₂')
  have hlog1 : Real.log (|T| + 3) ≤ L := by
    rw [abs_of_pos (by linarith)]; exact Real.log_le_log (by linarith) (by linarith)
  have hlog2 : Real.log (|T₂'| + 3) ≤ L := by
    rw [abs_of_pos (by linarith)]; exact Real.log_le_log (by linarith) (by linarith)
  have hfar := ncard_farZeros_le (2 * a / L) T (2 * T)
  have hsplit := N0simpleIsolated_le_band_add_far (5 / (2 * l T)) (2 * a / L) T (2 * T)
  have hsplitR : (N0simpleIsolated (5 / (2 * l T)) T (2 * T) : ℝ) ≤
      N0simpleIsolatedBand (5 / (2 * l T)) (2 * a / L) T (2 * T) +
        2 * ((rightFarZeros (2 * a / L) T (2 * T)).ncard : ℝ) := by
    have := hsplit.trans (Nat.add_le_add_left hfar _)
    exact_mod_cast this
  -- the deficit
  have hdef := band_deficit_arith (A := A) (K := K) (A₀ := A₀) (L := L) (T := T) (a := a)
    (E := Real.exp (-(a / 1200))) (S := S) hA.le hK (by linarith) hL1 ha1 (by linarith)
    (Real.exp_pos _).le hright (hend1.trans (mul_le_mul_of_nonneg_left hlog1 (by linarith)))
    (hend2.trans (mul_le_mul_of_nonneg_left hlog2 (by linarith))) hSle
  have hisoR : (HD 1 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simpleIsolated (5 / (2 * l T)) T (2 * T) :=
    hiso
  linarith

end

end RHTower
