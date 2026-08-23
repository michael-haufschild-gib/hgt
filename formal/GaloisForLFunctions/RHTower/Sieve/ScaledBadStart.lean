import GaloisForLFunctions.RHTower.Sieve.ScaledFibreStepOne
import GaloisForLFunctions.RHTower.Sieve.MarkerScaleTransfer

/-!
# The exceptional starts at a shrunk window

Step 1 says that all but `o(√y)` of the outer factors of `outerBlock y h` carry a fibre with a
definite proportion of each Möbius sign.  A marker is indexed by its *start*, not by an outer
factor, so what the marker join consumes is the image of the exceptional outer factors under the
start map — a set of integers of the same size — together with the fact that every start in the
range `[√y/2, √y − 1]` outside that image is realised by a good outer factor.
-/

namespace RHTower.Sieve

open Finset Filter Topology ArithmeticFunction

/-- The fibre above `a` carries a definite proportion of each Möbius sign. -/
noncomputable def goodFibre (y hy : ℝ) (a : ℕ) : Prop :=
  (3 / 16) * squarefreeDensity * (fibreLen y hy a : ℝ)
      ≤ (((Finset.Ioc (fibreStartIdx y a) (fibreStartIdx y a + fibreLen y hy a)).filter
          (fun n => moebius n = 1)).card : ℝ)
    ∧ (3 / 16) * squarefreeDensity * (fibreLen y hy a : ℝ)
      ≤ (((Finset.Ioc (fibreStartIdx y a) (fibreStartIdx y a + fibreLen y hy a)).filter
          (fun n => moebius n = -1)).card : ℝ)

open Classical in
/-- The exceptional outer factors. -/
noncomputable def badOuter (y hy : ℝ) : Finset ℕ :=
  (outerBlock y hy).filter (fun a => ¬ goodFibre y hy a)

open Classical in
/-- The exceptional starts. -/
noncomputable def badStart (y hy : ℝ) : Finset ℕ := (badOuter y hy).image (fibreStartIdx y)

theorem card_badStart_le_card_badOuter (y hy : ℝ) :
    (badStart y hy).card ≤ (badOuter y hy).card := by
  classical
  rw [badStart]
  exact Finset.card_image_le

open Classical in
/-- **The exceptional outer factors are `o(√y)` at a shrunk window.** -/
theorem eventually_card_badOuter_le {c β : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop,
      ((badOuter y (scaledLength c β y)).card : ℝ)
        ≤ 1024 * ε * Real.sqrt y / squarefreeDensity ^ 2 + Real.sqrt y / (Real.log y) ^ 2 := by
  filter_upwards [eventually_fibre_step_one_growing_scaled hc0 hc1 hβ0 hβ1 hε] with y hy
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := outerBlock y (scaledLength c β y)) (p := fun a => goodFibre y (scaledLength c β y) a)
  have hcast : (((outerBlock y (scaledLength c β y)).filter
        (fun a => goodFibre y (scaledLength c β y) a)).card : ℝ)
      + ((badOuter y (scaledLength c β y)).card : ℝ)
      = ((outerBlock y (scaledLength c β y)).card : ℝ) := by
    rw [badOuter]
    exact_mod_cast hsplit
  have hgoodeq : ((outerBlock y (scaledLength c β y)).filter
        (fun a => goodFibre y (scaledLength c β y) a))
      = ((outerBlock y (scaledLength c β y)).filter (fun a =>
          (3 / 16) * squarefreeDensity * (fibreLen y (scaledLength c β y) a : ℝ)
              ≤ (((Finset.Ioc (fibreStartIdx y a)
                  (fibreStartIdx y a + fibreLen y (scaledLength c β y) a)).filter
                  (fun n => moebius n = 1)).card : ℝ)
            ∧ (3 / 16) * squarefreeDensity * (fibreLen y (scaledLength c β y) a : ℝ)
              ≤ (((Finset.Ioc (fibreStartIdx y a)
                  (fibreStartIdx y a + fibreLen y (scaledLength c β y) a)).filter
                  (fun n => moebius n = -1)).card : ℝ))) := by
    refine Finset.filter_congr fun a _ => ?_
    rw [goodFibre]
  rw [hgoodeq] at hcast
  linarith [hy, hcast]

/-- **Every start outside the exceptional image is carried by a good outer factor.** -/
theorem exists_goodFibre_of_start {y hy : ℝ} {t : ℕ} (hy0 : 0 ≤ hy) (hy4 : 4 ≤ y)
    (ht1 : 1 ≤ t) (htlow : Real.sqrt y / 2 ≤ (t : ℝ)) (hthigh : (t : ℝ) + 1 ≤ Real.sqrt y)
    (hnot : t ∉ badStart y hy) :
    ∃ a, 1 ≤ a ∧ a ∈ outerBlock y hy ∧ fibreStartIdx y a = t ∧ goodFibre y hy a
      ∧ y / ((t : ℝ) + 1) ≤ (a : ℝ) ∧ (a : ℝ) < y / (t : ℝ) := by
  classical
  have hy0' : (0 : ℝ) < y := by linarith
  have hsy : (0 : ℝ) < Real.sqrt y := Real.sqrt_pos.2 hy0'
  have hsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt (by linarith)
  have htR : (0 : ℝ) < (t : ℝ) := by
    have : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
    linarith
  have hprod : ((t : ℝ) + 1) * (t : ℝ) ≤ y := by
    nlinarith [hthigh, htlow, hsq, hsy, htR]
  obtain ⟨a, ha1, halow, hahigh⟩ := exists_start_preimage ht1 hprod
  have haR : (0 : ℝ) < (a : ℝ) := by
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
    linarith
  have hstart : fibreStartIdx y a = t :=
    fibreStartIdx_eq_of_start_interval ht1 ha1 halow hahigh
  -- the outer factor sits in the dyadic block
  have hsqle : Real.sqrt y ≤ (a : ℝ) := by
    have hden : (0 : ℝ) < (t : ℝ) + 1 := by linarith
    have : y / ((t : ℝ) + 1) ≥ y / Real.sqrt y := by
      exact div_le_div_of_nonneg_left (by linarith) hden hthigh
    have hyy : y / Real.sqrt y = Real.sqrt y := by
      rw [eq_comm, eq_div_iff (ne_of_gt hsy)]
      linarith [hsq]
    rw [hyy] at this
    linarith [halow]
  have hle2 : (a : ℝ) ≤ 2 * Real.sqrt y := by
    have hlt : (a : ℝ) < y / (t : ℝ) := hahigh
    have hdiv : y / (t : ℝ) ≤ y / (Real.sqrt y / 2) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) htlow
    have hval : y / (Real.sqrt y / 2) = 2 * Real.sqrt y := by
      rw [eq_comm, eq_div_iff (by positivity)]
      nlinarith [hsq]
    rw [hval] at hdiv
    linarith
  have hmem : a ∈ outerBlock y hy := by
    rw [mem_outerBlock]
    refine ⟨⟨ha1, ?_⟩, hsqle, hle2⟩
    refine Nat.le_floor ?_
    have hpos : (0 : ℝ) ≤ hy * Real.sqrt y := mul_nonneg hy0 hsy.le
    nlinarith [hle2, hsq, hsy]
  refine ⟨a, ha1, hmem, hstart, ?_, halow, hahigh⟩
  by_contra hbad
  exact hnot (by
    rw [badStart, Finset.mem_image]
    exact ⟨a, by rw [badOuter, Finset.mem_filter]; exact ⟨hmem, hbad⟩, hstart⟩)

end RHTower.Sieve
