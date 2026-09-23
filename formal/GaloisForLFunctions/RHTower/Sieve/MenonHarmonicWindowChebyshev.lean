import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicWindowLadderAssembly

/-!
# The base case of the large-values hierarchy for the window super-level set

The window estimate leaves the measure of the exceptional set free, to be supplied by a
large-values theorem.  Its base case is Chebyshev: a set on which the polynomial exceeds `V` has
measure at most the polynomial's own mean square divided by `V²`.  This file supplies it, and the
resulting closed form of the window estimate in which the exceptional measure has been eliminated
in favour of any mean-square majorant.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **Chebyshev for a window super-level set.** -/
theorem volume_windowSuperLevel_le
    {F : ℝ → ℂ} (hF : Continuous F) {W V : ℝ} (_hW : 0 ≤ W) (hV : 0 < V) :
    volume.real (windowSuperLevel F W V)
      ≤ (∫ w in Set.Icc (-W) W, ‖F w‖ ^ (2 : ℕ)) / V ^ (2 : ℕ) := by
  classical
  set S : Set ℝ := windowSuperLevel F W V with hSdef
  have hSm : MeasurableSet S := measurableSet_windowSuperLevel hF W V
  have hSs : S ⊆ Set.Icc (-W) W := windowSuperLevel_subset F W V
  have hcont : Continuous fun w : ℝ => ‖F w‖ ^ (2 : ℕ) := (hF.norm).pow 2
  have hfin : volume S ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hSs)
    simp [Real.volume_Icc]
  have hint : IntegrableOn (fun w : ℝ => ‖F w‖ ^ (2 : ℕ)) (Set.Icc (-W) W) volume :=
    hcont.integrableOn_Icc
  have hintS : IntegrableOn (fun w : ℝ => ‖F w‖ ^ (2 : ℕ)) S volume := hint.mono_set hSs
  have hconstS : IntegrableOn (fun _ : ℝ => V ^ (2 : ℕ)) S volume :=
    integrableOn_const (by exact hfin) (by simp)
  have hlow : V ^ (2 : ℕ) * volume.real S ≤ ∫ w in S, ‖F w‖ ^ (2 : ℕ) := by
    have hmono := setIntegral_mono_on hconstS hintS hSm fun w hw => by
      have hwv : V < ‖F w‖ := hw.2
      nlinarith [norm_nonneg (F w), hV]
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm] at hmono
    exact hmono
  have hsub : (∫ w in S, ‖F w‖ ^ (2 : ℕ)) ≤ ∫ w in Set.Icc (-W) W, ‖F w‖ ^ (2 : ℕ) :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun w => by positivity)
      (LE.le.eventuallyLE hSs)
  have hV2 : (0 : ℝ) < V ^ (2 : ℕ) := by positivity
  rw [le_div_iff₀ hV2]
  calc
    volume.real S * V ^ (2 : ℕ) = V ^ (2 : ℕ) * volume.real S := by ring
    _ ≤ ∫ w in S, ‖F w‖ ^ (2 : ℕ) := hlow
    _ ≤ ∫ w in Set.Icc (-W) W, ‖F w‖ ^ (2 : ℕ) := hsub

/-- **The window estimate with the exceptional measure eliminated by any mean-square majorant.** -/
theorem integral_Icc_normSq_harmonicRamareBilinear_le_threshold_chebyshev
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W V I : ℝ} (k : ℕ) (hk : 1 ≤ k)
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L) (hV : 0 < V)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hmass : ∀ j ∈ Finset.range L,
      0 < harmonicPrimeMass (geomBlock P Q (1 + eta) j))
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (V₀ : ℕ → ℝ) (hV₀ : ∀ j ∈ Finset.range L, 0 < V₀ j)
    (J : ℕ → ℕ)
    (hJ : ∀ j ∈ Finset.range L,
      harmonicPrimeMass (geomBlock P Q (1 + eta) j) ≤ 2 ^ (J j) * V₀ j)
    (hI : (∫ w in Set.Icc (-W) W,
      ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ)) ≤ I) :
    (∫ w in Set.Icc (-W) W, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ))
      ≤ V ^ (2 : ℕ) * (2 * W)
        + harmonicPrimeMass P * ∑ j ∈ Finset.range L,
            menonHarmonicLevelTrivialBlockCost P A₀ B₀ Q eta W (I / V ^ (2 : ℕ)) k j (J j) (V₀ j)
              / harmonicPrimeMass (geomBlock P Q (1 + eta) j) := by
  classical
  have hcont := continuous_harmonicRamareBilinear P (Finset.Icc A₀ B₀)
  have hsplit := integral_Icc_normSq_le_threshold_add_superLevel (F :=
    fun w => harmonicRamareBilinear P (Finset.Icc A₀ B₀) w) hcont (V := V)
    (by linarith : (0 : ℝ) ≤ W)
  have hvol : volume.real
      (windowSuperLevel (harmonicRamareBilinear P (Finset.Icc A₀ B₀)) W V)
      ≤ I / V ^ (2 : ℕ) := by
    refine (volume_windowSuperLevel_le hcont (by linarith) hV).trans ?_
    exact div_le_div_of_nonneg_right hI (by positivity)
  have hlad := setIntegral_normSq_harmonicRamareBilinear_le_levelTrivial_mass
    (B₀ := B₀) k hk hA₀ hQ heta
    hW hL hPprime hPrange hmass hleft V₀ hV₀ J hJ
    (measurableSet_windowSuperLevel hcont W V) (windowSuperLevel_subset _ W V)
  have hPmass : (0 : ℝ) ≤ harmonicPrimeMass P :=
    Finset.sum_nonneg fun p _ => by positivity
  have hmono : harmonicPrimeMass P * ∑ j ∈ Finset.range L,
        menonHarmonicLevelTrivialBlockCost P A₀ B₀ Q eta W
            (volume.real
              (windowSuperLevel (harmonicRamareBilinear P (Finset.Icc A₀ B₀)) W V))
            k j (J j) (V₀ j)
          / harmonicPrimeMass (geomBlock P Q (1 + eta) j)
      ≤ harmonicPrimeMass P * ∑ j ∈ Finset.range L,
        menonHarmonicLevelTrivialBlockCost P A₀ B₀ Q eta W (I / V ^ (2 : ℕ)) k j (J j) (V₀ j)
          / harmonicPrimeMass (geomBlock P Q (1 + eta) j) := by
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) hPmass
    refine div_le_div_of_nonneg_right ?_ (hmass j hj).le
    rw [menonHarmonicLevelTrivialBlockCost, menonHarmonicLevelTrivialBlockCost]
    have hmassD : (0 : ℝ) ≤
        harmonicPrimeMass (harmonicGeomCofactorBlock A₀ B₀ Q eta j) ^ (2 : ℕ) := by positivity
    have hstep : volume.real
        (windowSuperLevel (harmonicRamareBilinear P (Finset.Icc A₀ B₀)) W V) *
          harmonicPrimeMass (harmonicGeomCofactorBlock A₀ B₀ Q eta j) ^ (2 : ℕ)
        ≤ (I / V ^ (2 : ℕ)) *
          harmonicPrimeMass (harmonicGeomCofactorBlock A₀ B₀ Q eta j) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right hvol hmassD
    have hV₀j : (0 : ℝ) ≤ V₀ j ^ (2 : ℕ) := by positivity
    nlinarith [hstep, hV₀j]
  exact hsplit.trans (add_le_add le_rfl (hlad.trans hmono))

end

end RHTower.Sieve
