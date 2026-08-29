import GaloisForLFunctions.HTGeometry.RamificationSubstitution
import GaloisForLFunctions.HTGeometry.LogPolyNegligible

/-!
# The Nevanlinna error term is negligible at a sequence of radii

The error term of the second main theorem is the sum of the proximities of the logarithmic
derivatives `f'/(f − a_j)` and `f'/f`.  At a Borel-good radius each of them is bounded by the
logarithm of a quantity polynomial in the radius and in the characteristic, and such a quantity is
`o(T(r,f))` whenever the characteristic outgrows every logarithm.

The good radii form a sequence tending to infinity, along which the characteristic also agrees with
the monotone majorant used by the Borel lemma.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Real ValueDistribution MeromorphicOn Filter Set

/-- **The error term of the second main theorem is negligible along a sequence of radii.** -/
theorem exists_good_radii_error_negligible {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {q : ℕ} (A : Fin q → ℂ)
    (hf0 : ∀ z, meromorphicOrderAt f z ≠ ⊤)
    (hfa : ∀ j, ∀ z, meromorphicOrderAt (fun w => f w - A j) z ≠ ⊤)
    (hTlog : Tendsto (fun r => Real.log r / charMajorant f r) atTop (nhds 0))
    (hTtop : Tendsto (charMajorant f) atTop atTop) :
    ∃ rn : ℕ → ℝ, Tendsto rn atTop atTop ∧
      (∀ᶠ n in atTop, charMajorant f (rn n) = characteristic f ⊤ (rn n)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        (∑ j, proximity (fun z => deriv f z / (f z - A j)) ⊤ (rn n))
          + proximity (fun z => deriv f z / f z) ⊤ (rn n)
        ≤ ε * charMajorant f (rn n)) := by
  classical
  have hmf : Meromorphic f := fun z => (hf.analyticAt z).meromorphicAt
  -- a majorant common to `f` and all the shifts
  have hposlog : ∀ x : ℝ, (0 : ℝ) ≤ Real.posLog x := fun x => le_max_left _ _
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hnn : ∀ i : Fin q, (0 : ℝ) ≤ Real.posLog ‖A i‖ + Real.log 2 :=
    fun i => add_nonneg (hposlog _) hlog2
  set Kshift : ℝ := ∑ j, (Real.posLog ‖A j‖ + Real.log 2) with hKs
  have hKs0 : 0 ≤ Kshift := Finset.sum_nonneg fun j _ => hnn j
  set U : ℝ → ℝ := fun s => charMajorant f s + Kshift + 1 with hU
  have hUmono : Monotone U := fun a b hab => by
    have h := monotone_charMajorant hmf hab
    simp only [hU]
    linarith
  have hU1 : ∀ s, 1 ≤ U s := fun s => by
    have h := one_le_charMajorant f s
    simp only [hU]
    linarith
  have hUdomf : ∀ s, 1 ≤ s → characteristic f ⊤ s ≤ U s := fun s hs => by
    have h := characteristic_le_charMajorant (f := f) hs
    simp only [hU]
    linarith
  have hUdoma : ∀ j : Fin q, ∀ s, 1 ≤ s →
      characteristic (fun w => f w - A j) ⊤ s ≤ U s := by
    intro j s hs
    have hshift := ValueDistribution.abs_characteristic_sub_characteristic_shift_le
      (f := f) (a₀ := A j) (r := s) hmf
    have h1 := (abs_le.mp hshift).1
    have h2 := characteristic_le_charMajorant (f := f) hs
    have hjle : Real.posLog ‖A j‖ + Real.log 2 ≤ Kshift := by
      rw [hKs]
      exact Finset.single_le_sum (f := fun i : Fin q => Real.posLog ‖A i‖ + Real.log 2)
        (fun i _ => hnn i) (Finset.mem_univ j)
    simp only [hU]
    linarith [h1, h2, hjle]
  -- good radii
  obtain ⟨rn, hrntop, hrn⟩ := exists_good_radius_seq hUmono hU1
  -- the polynomial bounds
  obtain ⟨C₀, hC₀0, hbnd₀⟩ := exists_logDeriv_poly_bound hf hf0 U hUmono hU1 hUdomf
  have hCjex : ∀ j : Fin q, ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → U (r + (U r)⁻¹) < 2 * U r →
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
        Real.posLog ‖logDeriv (fun w => f w - A j) ((r : ℂ) * Complex.exp (θ * Complex.I))‖
        ≤ 2 * Real.log (1 + C * (r + 1) ^ 4 * (U r + 1) ^ 4) :=
    fun j => exists_logDeriv_poly_bound (hf.sub_const (A j)) (hfa j) U hUmono hU1 (hUdoma j)
  choose Cj hCj0 hbndj using hCjex
  set Cmax : ℝ := C₀ + ∑ j, Cj j with hCmax
  have hCmax0 : 0 ≤ Cmax := by
    have : (0 : ℝ) ≤ ∑ j, Cj j := Finset.sum_nonneg fun j _ => hCj0 j
    rw [hCmax]
    linarith
  have hC₀le : C₀ ≤ Cmax := by
    have : (0 : ℝ) ≤ ∑ j, Cj j := Finset.sum_nonneg fun j _ => hCj0 j
    rw [hCmax]
    linarith
  have hCjle : ∀ j, Cj j ≤ Cmax := by
    intro j
    have h1 : Cj j ≤ ∑ i, Cj i := Finset.single_le_sum (fun i _ => hCj0 i) (Finset.mem_univ j)
    rw [hCmax]
    linarith
  -- the error term
  set S : ℝ → ℝ := fun r => (∑ j, proximity (fun z => deriv f z / (f z - A j)) ⊤ r)
    + proximity (fun z => deriv f z / f z) ⊤ r with hSdef
  have hUplus : ∀ r : ℝ, U r + 1 ≤ (Kshift + 2) * (charMajorant f r + 1) := by
    intro r
    have h1 := one_le_charMajorant f r
    have h2 : (0 : ℝ) ≤ Kshift * charMajorant f r := mul_nonneg hKs0 (by linarith only [h1])
    simp only [hU]
    nlinarith [h1, hKs0, h2]
  have hSbound : ∀ n : ℕ, 1 ≤ rn n →
      S (rn n) ≤ 2 * ((q : ℝ) + 1)
        * Real.log (1 + Cmax * (Kshift + 2) ^ 4 * (rn n + 1) ^ 4
          * (charMajorant f (rn n) + 1) ^ 4) := by
    intro n hrn1
    have hgoodn := (hrn n).2
    set r : ℝ := rn n with hrdef
    have hUr1 : (1 : ℝ) ≤ U r := hU1 r
    have hCM1 : (1 : ℝ) ≤ charMajorant f r := one_le_charMajorant f r
    have hr1' : (1 : ℝ) ≤ r + 1 := by linarith
    -- the common right-hand side
    have hstep : ∀ C : ℝ, 0 ≤ C → C ≤ Cmax →
        2 * Real.log (1 + C * (r + 1) ^ 4 * (U r + 1) ^ 4)
          ≤ 2 * Real.log (1 + Cmax * (Kshift + 2) ^ 4 * (r + 1) ^ 4
            * (charMajorant f r + 1) ^ 4) := by
      intro C hC0 hCle
      refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) (by norm_num)
      have hpow : (U r + 1) ^ 4 ≤ (Kshift + 2) ^ 4 * (charMajorant f r + 1) ^ 4 := by
        have h1 := hUplus r
        have h2 : (0 : ℝ) ≤ U r + 1 := by linarith
        calc (U r + 1) ^ 4 ≤ ((Kshift + 2) * (charMajorant f r + 1)) ^ 4 :=
              pow_le_pow_left₀ h2 h1 4
          _ = (Kshift + 2) ^ 4 * (charMajorant f r + 1) ^ 4 := by ring
      have hposr : (0 : ℝ) ≤ (r + 1) ^ 4 := by positivity
      have hstep1 : C * (r + 1) ^ 4 * (U r + 1) ^ 4
          ≤ Cmax * (r + 1) ^ 4 * ((Kshift + 2) ^ 4 * (charMajorant f r + 1) ^ 4) := by
        refine mul_le_mul ?_ hpow (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hCle hposr
      linarith only [hstep1]
    have hj : ∀ j : Fin q, proximity (fun z => deriv f z / (f z - A j)) ⊤ r
        ≤ 2 * Real.log (1 + Cmax * (Kshift + 2) ^ 4 * (r + 1) ^ 4
          * (charMajorant f r + 1) ^ 4) := by
      intro j
      rw [proximity_logDeriv_sub_const_eq hf (A j)]
      exact le_trans (hbndj j r hrn1 hgoodn) (hstep (Cj j) (hCj0 j) (hCjle j))
    have hzero : proximity (fun z => deriv f z / f z) ⊤ r
        ≤ 2 * Real.log (1 + Cmax * (Kshift + 2) ^ 4 * (r + 1) ^ 4
          * (charMajorant f r + 1) ^ 4) := by
      rw [proximity_logDeriv_eq]
      exact le_trans (hbnd₀ r hrn1 hgoodn) (hstep C₀ hC₀0 hC₀le)
    have hsum : (∑ j, proximity (fun z => deriv f z / (f z - A j)) ⊤ r)
        ≤ (q : ℝ) * (2 * Real.log (1 + Cmax * (Kshift + 2) ^ 4 * (r + 1) ^ 4
          * (charMajorant f r + 1) ^ 4)) := by
      have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin q))) => hj j)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
      exact h
    simp only [hSdef]
    linarith only [hsum, hzero]
  -- negligibility of the error term
  have hneg : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, S (rn n) ≤ ε * charMajorant f (rn n) := by
    intro ε hε
    refine eventually_le_of_log_poly_bound_filter (ρ := fun n => rn n)
      (C := Cmax * (Kshift + 2) ^ 4) (k := 4)
      (c := 2 * ((q : ℝ) + 1)) (by positivity) (by omega) (by positivity) ?_ ?_ ?_ ?_ ?_ hε
    · filter_upwards [hrntop.eventually_ge_atTop (1 : ℝ)] with n hn
      exact hSbound n hn
    · exact Filter.Eventually.of_forall fun n => one_le_charMajorant f (rn n)
    · exact hrntop.eventually_ge_atTop (2 : ℝ)
    · exact hTlog.comp hrntop
    · exact hTtop.comp hrntop
  have hTeq : ∀ᶠ r in atTop, charMajorant f r = characteristic f ⊤ r := by
    filter_upwards [hTtop.eventually_gt_atTop (1 : ℝ), eventually_ge_atTop (1 : ℝ)] with r h1 hr
    have hmax : charMajorant f r = max (characteristic f ⊤ r) 1 := by
      rw [charMajorant, max_eq_left hr]
    rw [hmax] at h1 ⊢
    refine max_eq_left ?_
    rcases le_or_gt (characteristic f ⊤ r) 1 with h | h
    · rw [max_eq_right h] at h1
      linarith
    · linarith
  refine ⟨rn, hrntop, hrntop.eventually hTeq, ?_⟩
  intro ε hε
  have := hneg ε hε
  simpa only [hSdef] using this

end GaloisForLFunctions.HTGeometry
