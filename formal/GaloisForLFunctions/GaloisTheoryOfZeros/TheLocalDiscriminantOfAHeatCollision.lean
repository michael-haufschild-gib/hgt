import GaloisForLFunctions.GaloisTheoryOfZeros.TheCentreValueIsTheEquationOfTheSignBranchPoints
import GaloisForLFunctions.GaloisTheoryOfZeros.NoZeroEscapesOverForwardTimes
import GaloisForLFunctions.Bottcher.EvenHoloExtension
import GaloisForLFunctions.HTGeometry.RectangleResidue
import Mathlib.Data.Sym.Card

/-!
# The local discriminant of a heat collision

Over the square root of the time displacement, the difference of any two
Hermite sheets has a simple zero. The product over ordered distinct pairs
is the discriminant up to a constant sign. It descends to the original time
disc with order `m.choose 2`. Its logarithmic derivative recovers this
integer on the boundary of every sufficiently small enclosing rectangle.
-/

open Complex Set Filter Topology Metric
open scoped ENNReal
open RHTower RHTower.DeBruijn GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section

variable {τ z : ℂ} {m : ℕ}

private def rootDifferences (m : ℕ) (f : ℝ → ℂ) : ℂ :=
  ∏ p ∈ (profileRoots m).offDiag, (f p.1 - f p.2)

/-- Signed discriminant of all sheets through the marked heat zero, at time `τ + s²`. -/
def collisionSheetDiscriminant (τ z : ℂ) (m : ℕ) (s : ℂ) : ℂ :=
  rootDifferences m fun r => collisionZero τ z m r s

private theorem mem_profileRoots_neg {r : ℝ} (hr : r ∈ profileRoots m) :
    -r ∈ profileRoots m := by
  have h : heatModelFwd m (- (r : ℂ)) = 0 := by
    rw [heatModelFwd_neg, heatModelFwd_profileRoot hr, mul_zero]
  obtain ⟨q, hq, he⟩ := heatModelFwd_eq_zero_iff.mp h
  have hqr : q = -r := Complex.ofReal_injective (by simpa using he)
  rwa [hqr] at hq

private theorem rootDifferences_neg (f : ℝ → ℂ) :
    (rootDifferences m fun r => f (-r)) = rootDifferences m f := by
  unfold rootDifferences
  refine Finset.prod_bij (fun p _ => (-p.1, -p.2)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro p hp
    obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
    exact Finset.mem_offDiag.mpr
      ⟨mem_profileRoots_neg ha, mem_profileRoots_neg hb, fun h => hab (neg_injective h)⟩
  · rintro ⟨a,b⟩ _ ⟨c,d⟩ _ he
    simpa using he
  · rintro ⟨a,b⟩ hp
    obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
    exact ⟨(-a,-b), Finset.mem_offDiag.mpr
      ⟨mem_profileRoots_neg ha, mem_profileRoots_neg hb, fun h => hab (neg_injective h)⟩,
      by simp⟩

private theorem collisionSheetDiscriminant_even (hc : IsCollision τ z m) :
    ∀ᶠ s in 𝓝 0, collisionSheetDiscriminant τ z m (-s) =
      collisionSheetDiscriminant τ z m s := by
  classical
  have h : ∀ᶠ s in 𝓝 0, ∀ r ∈ profileRoots m, collisionZero τ z m r (-s) =
      collisionZero τ z m ((-r : ℝ) : ℂ) s := by
    rw [Filter.eventually_all_finset]
    intro r hr
    simpa only [Complex.ofReal_neg] using collisionZero_neg hc (heatModelFwd_profileRoot hr)
  filter_upwards [h] with s hs
  unfold collisionSheetDiscriminant
  rw [← rootDifferences_neg (m := m) (fun r => collisionZero τ z m r s)]
  apply Finset.prod_congr rfl
  intro p hp
  obtain ⟨ha, hb, _⟩ := Finset.mem_offDiag.mp hp
  exact congrArg₂ (· - ·) (hs _ ha) (hs _ hb)

private theorem disc_factor (s : ℂ) :
    collisionSheetDiscriminant τ z m s = (s ^ 2) ^ (m.choose 2) *
      rootDifferences m (fun r => collisionBranch τ z m r s) := by
  classical
  have hcard := Sym2.two_mul_card_image_offDiag (profileRoots m)
  rw [Sym2.card_image_offDiag, card_profileRoots] at hcard
  unfold collisionSheetDiscriminant rootDifferences
  simp_rw [collisionZero, add_sub_add_left_eq_sub, ← mul_sub]
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul, hcard]

private theorem disc_unit (hc : IsCollision τ z m) :
    ∃ V : ℂ → ℂ, AnalyticAt ℂ V 0 ∧ V 0 ≠ 0 ∧
      ∀ᶠ s in 𝓝 0, collisionSheetDiscriminant τ z m s =
        (s ^ 2) ^ (m.choose 2) * V (s ^ 2) := by
  classical
  let U (s : ℂ) := rootDifferences m (fun r => collisionBranch τ z m r s)
  have hU : AnalyticAt ℂ U 0 := by
    apply Finset.analyticAt_fun_prod
    intro ⟨a,b⟩ hp
    obtain ⟨ha, hb, _⟩ := Finset.mem_offDiag.mp hp
    exact (collisionBranch_spec hc (heatModelFwd_profileRoot ha)).1.sub
      (collisionBranch_spec hc (heatModelFwd_profileRoot hb)).1
  have hu : U 0 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ⟨a,b⟩ hp
    obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
    change collisionBranch τ z m (a : ℂ) 0 - collisionBranch τ z m (b : ℂ) 0 ≠ 0
    rw [(collisionBranch_spec hc (heatModelFwd_profileRoot (r := a) ha)).2.1,
      (collisionBranch_spec hc (heatModelFwd_profileRoot hb)).2.1]
    exact sub_ne_zero.mpr (fun h => hab (Complex.ofReal_injective h))
  have hev : ∀ᶠ s in 𝓝 0, U (-s) = U s := by
    filter_upwards [collisionSheetDiscriminant_even hc] with s hs
    by_cases h : s = 0
    · simp [h]
    · rw [disc_factor, disc_factor, neg_sq] at hs
      exact mul_left_cancel₀ (pow_ne_zero _ (pow_ne_zero _ h)) hs
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hU.eventually_analyticAt.and hev)
  obtain ⟨V, hV, he⟩ := Bottcher.exists_analytic_factor_of_even hR
    (fun s hs => (hball hs).1.differentiableAt.differentiableWithinAt)
    (fun s hs => (hball hs).2)
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  refine ⟨V, hV.analyticAt (isOpen_ball.mem_nhds (mem_ball_self (sq_pos_of_pos hR))), ?_, ?_⟩
  · have he0 : V 0 = U 0 := by simpa using he 0 h0
    exact he0.symm ▸ hu
  · filter_upwards [ball_mem_nhds (0 : ℂ) hR] with s hs
    rw [he s hs, disc_factor]

/-- In the original time coordinate the local sheet discriminant has order
`m.choose 2`. Its boundary integral counts every pair, with location retained
by the choice of the isolating cluster. The time coordinate here is `w = t − τ`. -/
theorem IsCollision.exists_discriminant_winding (hc : IsCollision τ z m) :
    ∃ D : ℂ → ℂ, AnalyticAt ℂ D 0 ∧
      (∀ᶠ s in 𝓝 0, D (s ^ 2) = collisionSheetDiscriminant τ z m s) ∧
      analyticOrderAt D 0 = (m.choose 2 : ℕ∞) ∧
      ∃ R > 0, ∀ a b : ℂ, a.re < 0 → 0 < b.re → a.im < 0 → 0 < b.im →
        (uIcc a.re b.re ×ℂ uIcc a.im b.im) ⊆ ball 0 R →
        rectIntegral (logDeriv D) a b = 2 * Real.pi * I * (m.choose 2 : ℂ) := by
  obtain ⟨V, hV, h0, he⟩ := disc_unit hc
  let D (w : ℂ) := w ^ (m.choose 2) * V w
  have hD : AnalyticAt ℂ D 0 := (analyticAt_id.pow _).mul hV
  refine ⟨D, hD, he.mono (fun s hs => hs.symm),
    hD.analyticOrderAt_eq_natCast.mpr ⟨V, hV, h0, by simp [D]⟩, ?_⟩
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp
    (hV.eventually_analyticAt.and (hV.continuousAt.eventually_ne h0))
  refine ⟨R, hR, fun a b ha hb hc' hd hsub => ?_⟩
  simpa [D] using rectIntegral_logDeriv_single_zero (ρ := 0) (m := m.choose 2)
    (h := V) ha hb hc' hd hsub (fun w hw => (hball hw).1) (fun w hw => (hball hw).2)

/-- Local discriminant multiplicity at a marked time and place. It is zero at
regular points and at simple zeros. -/
def heatIntersectionMultiplicity (p : ℂ × ℂ) : ℕ :=
  (analyticOrderNatAt (complexHeat p.1) p.2).choose 2

theorem IsCollision.heatIntersectionMultiplicity_eq (h : IsCollision τ z m) :
    heatIntersectionMultiplicity (τ,z) = m.choose 2 := by
  simp only [heatIntersectionMultiplicity, analyticOrderNatAt, isCollision_iff_analyticOrderAt.mp h,
    ENat.toNat_coe]

theorem heatIntersectionMultiplicity_ne_zero_iff (p : ℂ × ℂ) :
    heatIntersectionMultiplicity p ≠ 0 ↔ p ∈ multipleZeros := by
  obtain ⟨τ,z⟩ := p
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_complexHeat_ne_top τ z)
  have hc := isCollision_iff_analyticOrderAt.mpr hm.symm
  rw [hc.heatIntersectionMultiplicity_eq, Nat.choose_ne_zero_iff]
  constructor
  · intro h
    exact ⟨by simpa using hc.vanish 0 (by omega),
      by simpa only [iteratedDeriv_one] using hc.vanish 1 (by omega)⟩
  · intro hp
    by_contra! h
    rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
    · exact hc.top_ne_zero (by simpa only [iteratedDeriv_zero] using hp.1)
    · exact hc.top_ne_zero (by simpa only [iteratedDeriv_one] using hp.2)

/-- Total intersection multiplicity in a window in time and place. A cut
may assign its seam to either half by choosing a half-open window. -/
def heatIntersectionMass (B : Set (ℂ × ℂ)) : ℝ≥0∞ :=
  ∑' p, B.indicator (fun q => (heatIntersectionMultiplicity q : ℝ≥0∞)) p

theorem heatIntersectionMass_union {A B : Set (ℂ × ℂ)} (h : Disjoint A B) :
    heatIntersectionMass (A ∪ B) = heatIntersectionMass A + heatIntersectionMass B := by
  classical
  simp only [heatIntersectionMass, Set.indicator_union_of_disjoint h, ENNReal.tsum_add]

/-- Points on a cut shared by two closed windows are counted exactly once. -/
theorem heatIntersectionMass_cut (A B : Set (ℂ × ℂ)) :
    heatIntersectionMass (A ∪ B) + heatIntersectionMass (A ∩ B) =
      heatIntersectionMass A + heatIntersectionMass B := by
  classical
  simp only [heatIntersectionMass, ← ENNReal.tsum_add]
  apply tsum_congr
  intro p
  by_cases ha : p ∈ A <;> by_cases hb : p ∈ B <;> simp [ha, hb]

theorem heatIntersectionMass_eq_zero_iff (B : Set (ℂ × ℂ)) :
    heatIntersectionMass B = 0 ↔ Disjoint B multipleZeros := by
  classical
  rw [heatIntersectionMass, ENNReal.tsum_eq_zero, Set.disjoint_left]
  constructor
  · intro h p hp hcoll
    have hz := h p
    rw [Set.indicator_of_mem hp, Nat.cast_eq_zero] at hz
    exact ((heatIntersectionMultiplicity_ne_zero_iff p).mpr hcoll) hz
  · intro h p
    by_cases hp : p ∈ B
    · rw [Set.indicator_of_mem hp, Nat.cast_eq_zero]
      exact not_ne_iff.mp (fun hn => h hp ((heatIntersectionMultiplicity_ne_zero_iff p).mp hn))
    · exact Set.indicator_of_notMem hp _

/-- Compact windows contain only finitely many terms, including for complex time. -/
theorem compact_heatIntersectionMass (B : Set (ℂ × ℂ)) (hB : IsCompact B) :
    ∃ S : Finset (ℂ × ℂ), (∀ p, p ∈ S ↔ p ∈ B ∧ p ∈ multipleZeros) ∧
      heatIntersectionMass B = ∑ p ∈ S, (heatIntersectionMultiplicity p : ℝ≥0∞) := by
  classical
  have hd := (isDiscrete_iff_discreteTopology.2 discreteTopology_multipleZeros).mono
    (Set.inter_subset_right (s := B) (t := multipleZeros))
  let S := ((hB.inter_right isClosed_multipleZeros).finite hd).toFinset
  have hs : ∀ p, p ∈ S ↔ p ∈ B ∧ p ∈ multipleZeros := by simp [S]
  refine ⟨S, hs, ?_⟩
  unfold heatIntersectionMass
  rw [tsum_eq_sum (s := S) (fun p hp => ?_)]
  · exact Finset.sum_congr rfl (fun p hp => Set.indicator_of_mem ((hs p).mp hp).1 _)
  · by_cases hb : p ∈ B
    · rw [Set.indicator_of_mem hb, Nat.cast_eq_zero]
      exact not_ne_iff.mp (fun hn => hp ((hs p).mpr
        ⟨hb, (heatIntersectionMultiplicity_ne_zero_iff p).mp hn⟩))
    · exact Set.indicator_of_notMem hb _

/-- Vanishing on any cover of all positive real times and all places is equivalent to RH. -/
theorem forall_heatIntersectionMass_eq_zero_iff_rh {ι : Type*} (B : ι → Set (ℂ × ℂ))
    (cover : ⋃ i, B i = {p | ∃ t : ℝ, 0 < t ∧ p.1 = (t : ℂ)}) :
    (∀ i, heatIntersectionMass (B i) = 0) ↔ RiemannHypothesis := by
  simp_rw [heatIntersectionMass_eq_zero_iff, Set.disjoint_left]
  rw [riemannHypothesis_iff_forall_pos_not_mem_branchTimes]
  constructor
  · rintro h t ht ⟨p, hp, he⟩
    have hmem : p ∈ ⋃ i, B i := by rw [cover]; exact ⟨t, ht, he⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    exact h i hi hp
  · intro h i p hp hc
    have hmem : p ∈ ⋃ i, B i := Set.mem_iUnion.mpr ⟨i,hp⟩
    rw [cover] at hmem
    obtain ⟨t, ht, he⟩ := hmem
    exact h t ht ⟨p, hc, he⟩


/-- Positive real times between `1/n` and `n`, with places of norm at most
`n`. The reciprocal condition also defines the empty zeroth window. -/
def realHeatWindow (n : ℕ) : Set (ℂ × ℂ) :=
  {p | ∃ t : ℝ, 0 < t ∧ p.1 = (t : ℂ) ∧ 1/t ≤ n ∧ t ≤ n ∧ ‖p.2‖ ≤ n}

/-- The fixed time and height exhaustion has zero intersection mass in
every window exactly when RH holds. -/
theorem realHeatWindow_vanishing_iff_rh :
    (∀ n, heatIntersectionMass (realHeatWindow n) = 0) ↔ RiemannHypothesis := by
  apply forall_heatIntersectionMass_eq_zero_iff_rh
  ext p
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨n,t,ht,he,_⟩
    exact ⟨t,ht,he⟩
  · rintro ⟨t,ht,he⟩
    obtain ⟨n,hn⟩ := exists_nat_ge (max (1/t) (max t ‖p.2‖))
    exact ⟨n,t,ht,he,(le_max_left _ _).trans hn,
      (le_max_left t _).trans ((le_max_right _ _).trans hn),
      (le_max_right t _).trans ((le_max_right _ _).trans hn)⟩

/-! ## Simultaneous clusters and changes of the height window -/

private def heatPlaceOrder (τ z : ℂ) := analyticOrderNatAt (complexHeat τ) z

private theorem isCollision_placeOrder (τ z : ℂ) : IsCollision τ z (heatPlaceOrder τ z) :=
  isCollision_iff_analyticOrderAt.mpr
    (Nat.cast_analyticOrderNatAt (analyticOrderAt_complexHeat_ne_top τ z)).symm

private theorem profile_prod_neg (m : ℕ) (f : ℝ → ℂ) :
    (∏ r ∈ profileRoots m, f (-r)) = ∏ r ∈ profileRoots m, f r := by
  refine Finset.prod_bij (fun r _ => -r) (fun _ => mem_profileRoots_neg)
    (fun _ _ _ _ h => neg_injective h) ?_ (fun _ _ => rfl)
  exact fun r hr => ⟨-r, mem_profileRoots_neg hr, neg_neg _⟩

/-- Resultant between two different clusters. Each ordered pair of centres
occurs once in the signed discriminant of the full window. -/
private def clusterResultant (τ a b s : ℂ) : ℂ :=
  ∏ r ∈ profileRoots (heatPlaceOrder τ a), ∏ q ∈ profileRoots (heatPlaceOrder τ b),
    (collisionZero τ a (heatPlaceOrder τ a) r s - collisionZero τ b (heatPlaceOrder τ b) q s)

private theorem analyticAt_sheet {r : ℝ} (hc : IsCollision τ z m) (hr : r ∈ profileRoots m) :
    AnalyticAt ℂ (collisionZero τ z m r) 0 :=
  analyticAt_const.add (analyticAt_id.mul (collisionBranch_spec hc (heatModelFwd_profileRoot hr)).1)

private theorem sheet_turn (τ a : ℂ) :
    ∀ᶠ s in 𝓝 0, ∀ r ∈ profileRoots (heatPlaceOrder τ a),
      collisionZero τ a (heatPlaceOrder τ a) r (-s) =
      collisionZero τ a (heatPlaceOrder τ a) ((-r : ℝ) : ℂ) s := by
  rw [Filter.eventually_all_finset]
  intro r hr
  simpa only [Complex.ofReal_neg] using
    collisionZero_neg (isCollision_placeOrder τ a) (heatModelFwd_profileRoot hr)

private theorem clusterResultant_unit (τ a b : ℂ) (hab : a ≠ b) :
    ∃ V : ℂ → ℂ, AnalyticAt ℂ V 0 ∧ V 0 ≠ 0 ∧
      ∀ᶠ s in 𝓝 0, V (s ^ 2) = clusterResultant τ a b s := by
  classical
  have hc : AnalyticAt ℂ (clusterResultant τ a b) 0 := by
    apply Finset.analyticAt_fun_prod
    intro r hr
    apply Finset.analyticAt_fun_prod
    intro q hq
    exact (analyticAt_sheet (isCollision_placeOrder τ a) hr).sub
      (analyticAt_sheet (isCollision_placeOrder τ b) hq)
  have h0 : clusterResultant τ a b 0 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro r _
    apply Finset.prod_ne_zero_iff.mpr
    intro q _
    simpa [collisionZero] using sub_ne_zero.mpr hab
  have hev : ∀ᶠ s in 𝓝 0, clusterResultant τ a b (-s) = clusterResultant τ a b s := by
    filter_upwards [sheet_turn τ a, sheet_turn τ b] with s ha hb
    unfold clusterResultant
    calc
      _ = ∏ r ∈ profileRoots (heatPlaceOrder τ a), ∏ q ∈ profileRoots (heatPlaceOrder τ b),
            (collisionZero τ a (heatPlaceOrder τ a) ((-r : ℝ) : ℂ) s -
             collisionZero τ b (heatPlaceOrder τ b) ((-q : ℝ) : ℂ) s) := by
              exact Finset.prod_congr rfl fun r hr => Finset.prod_congr rfl fun q hq =>
                congrArg₂ (· - ·) (ha r hr) (hb q hq)
      _ = _ := by
        rw [profile_prod_neg (heatPlaceOrder τ a) (fun r =>
          ∏ q ∈ profileRoots (heatPlaceOrder τ b),
          (collisionZero τ a (heatPlaceOrder τ a) r s -
           collisionZero τ b (heatPlaceOrder τ b) ((-q : ℝ) : ℂ) s))]
        exact Finset.prod_congr rfl (fun r _ => profile_prod_neg _ (fun q =>
          collisionZero τ a (heatPlaceOrder τ a) r s - collisionZero τ b (heatPlaceOrder τ b) q s))
  obtain ⟨R, hR, hr⟩ := Metric.mem_nhds_iff.mp (hc.eventually_analyticAt.and hev)
  obtain ⟨V, hV, he⟩ := Bottcher.exists_analytic_factor_of_even hR
    (fun s hs => (hr hs).1.differentiableAt.differentiableWithinAt) (fun s hs => (hr hs).2)
  have he0 : V 0 = clusterResultant τ a b 0 := by simpa using he 0 (mem_ball_self hR)
  exact ⟨V, hV.analyticAt (isOpen_ball.mem_nhds (mem_ball_self (sq_pos_of_pos hR))),
    he0.symm ▸ h0, Filter.mem_of_superset (ball_mem_nhds (0 : ℂ) hR) (fun _ hs => he _ hs)⟩

/-- Signed discriminant of all sheets through a finite set of marked places.
The second product retains differences between sheets in distinct clusters. -/
def heatWindowDiscriminant (τ : ℂ) (S : Finset ℂ) (s : ℂ) : ℂ :=
  (∏ a ∈ S, collisionSheetDiscriminant τ a (heatPlaceOrder τ a) s) *
    ∏ p ∈ S.offDiag, clusterResultant τ p.1 p.2 s

private theorem product_time_units {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ)
    (n : ι → ℕ) (units : ∀ i ∈ S, ∃ V : ℂ → ℂ, AnalyticAt ℂ V 0 ∧ V 0 ≠ 0 ∧
      ∀ᶠ s in 𝓝 0, F i s = (s ^ 2) ^ n i * V (s ^ 2)) :
    ∃ W : ℂ → ℂ, AnalyticAt ℂ W 0 ∧ W 0 ≠ 0 ∧
      ∀ᶠ s in 𝓝 0, (∏ i ∈ S, F i s) = (s ^ 2) ^ (∑ i ∈ S, n i) * W (s ^ 2) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 1, analyticAt_const, one_ne_zero, by simp⟩
  | insert i S hi ih =>
    obtain ⟨V,hV,hv,he⟩ := units i (Finset.mem_insert_self _ _)
    obtain ⟨W,hW,hw,hf⟩ := ih (fun j hj => units j (Finset.mem_insert_of_mem hj))
    refine ⟨fun w => V w * W w, hV.mul hW, mul_ne_zero hv hw, ?_⟩
    filter_upwards [he,hf] with s hs ht
    rw [Finset.prod_insert hi, Finset.sum_insert hi, hs, ht, pow_add]
    ring

private theorem heatWindow_factor (τ : ℂ) (S : Finset ℂ) :
    ∃ U : ℂ → ℂ, AnalyticAt ℂ U 0 ∧ U 0 ≠ 0 ∧ ∀ᶠ s in 𝓝 0,
      heatWindowDiscriminant τ S s =
        (s ^ 2) ^ (∑ z ∈ S, heatIntersectionMultiplicity (τ,z)) * U (s ^ 2) := by
  classical
  obtain ⟨V,hV,hv,he⟩ := product_time_units S
    (fun z => collisionSheetDiscriminant τ z (heatPlaceOrder τ z))
    (fun z => heatIntersectionMultiplicity (τ,z)) (fun z _ => disc_unit (isCollision_placeOrder τ z))
  obtain ⟨W,hW,hw,hf⟩ := product_time_units S.offDiag
    (fun p => clusterResultant τ p.1 p.2) (fun _ => 0) (by
      intro p hp
      obtain ⟨W,hW,hw,he⟩ := clusterResultant_unit τ p.1 p.2 (Finset.mem_offDiag.mp hp).2.2
      exact ⟨W,hW,hw, he.mono fun s hs => by simpa using hs.symm⟩)
  let U (w : ℂ) := V w * W w
  have hU : AnalyticAt ℂ U 0 := hV.mul hW
  have hu : U 0 ≠ 0 := mul_ne_zero hv hw
  refine ⟨U,hU,hu,?_⟩
  filter_upwards [he,hf] with s hs ht
  simp only [heatWindowDiscriminant, hs, ht, Finset.sum_const_zero, pow_zero, one_mul, U,
    mul_assoc]

/-- A rectangle around a time slice reads the sum of the actual local
multiplicities of its marked places. All inter-cluster resultants are analytic
units. Adding or removing a simple sheet therefore contributes zero winding. -/
theorem heatWindowDiscriminant_winding (τ : ℂ) (S : Finset ℂ) :
    ∃ D : ℂ → ℂ, AnalyticAt ℂ D 0 ∧
      (∀ᶠ s in 𝓝 0, D (s ^ 2) = heatWindowDiscriminant τ S s) ∧
      ∃ R > 0, ∀ a b : ℂ, a.re < 0 → 0 < b.re → a.im < 0 → 0 < b.im →
        (uIcc a.re b.re ×ℂ uIcc a.im b.im) ⊆ ball 0 R →
        rectIntegral (logDeriv D) a b =
          2 * Real.pi * I * ((∑ z ∈ S, heatIntersectionMultiplicity (τ,z) : ℕ) : ℂ) := by
  obtain ⟨U,hU,hu,he⟩ := heatWindow_factor τ S
  let n := ∑ z ∈ S, heatIntersectionMultiplicity (τ,z)
  refine ⟨fun w => w ^ n * U w, (analyticAt_id.pow _).mul hU, he.mono (fun _ h => h.symm), ?_⟩
  obtain ⟨R,hR,hr⟩ := Metric.mem_nhds_iff.mp
      (hU.eventually_analyticAt.and (hU.continuousAt.eventually_ne hu))
  refine ⟨R,hR, fun a b ha hb hc hd hsub => ?_⟩
  simpa only [zero_re, zero_im, sub_zero] using rectIntegral_logDeriv_single_zero
      (h := U) (m := n) (ρ := 0) ha hb hc hd hsub (fun w hw => (hr hw).1)
        (fun w hw => (hr hw).2)

/-- A global equation in the time plane for the projection of a finite
marked collision divisor. Equal times at different places retain both factors. -/
def projectedHeatDiscriminant (C : Finset (ℂ × ℂ)) (t : ℂ) : ℂ :=
  ∏ p ∈ C, (t-p.1) ^ heatIntersectionMultiplicity p

/-- Cutting time or place multiplies the two equations, with the shared
boundary divisor counted once. -/
theorem projectedHeatDiscriminant_cut (A B : Finset (ℂ × ℂ)) (t : ℂ) :
    projectedHeatDiscriminant (A ∪ B) t * projectedHeatDiscriminant (A ∩ B) t =
      projectedHeatDiscriminant A t * projectedHeatDiscriminant B t :=
  Finset.prod_union_inter

/-- Equality up to a holomorphic unit with the discriminant of the actual
sheets above each marked time. This identifies the projected divisor even
when several clusters collide at that time. -/
theorem projectedHeatDiscriminant_local (C : Finset (ℂ × ℂ)) (τ : ℂ) :
    let S := (C.filter (fun p => p.1 = τ)).image Prod.snd
    ∃ U : ℂ → ℂ, AnalyticAt ℂ U 0 ∧ U 0 ≠ 0 ∧
      ∀ᶠ s in 𝓝 0, projectedHeatDiscriminant C (τ + s ^ 2) =
        U (s ^ 2) * heatWindowDiscriminant τ S s := by
  classical
  let A := C.filter (fun p => p.1 = τ)
  let S := A.image Prod.snd
  let B := C.filter (fun p => ¬ p.1 = τ)
  let n := ∑ z ∈ S, heatIntersectionMultiplicity (τ,z)
  let L (w : ℂ) := projectedHeatDiscriminant B (τ+w)
  have hL : AnalyticAt ℂ L 0 := by
    apply Finset.analyticAt_fun_prod
    intro p _
    exact (((analyticAt_const.add analyticAt_id).sub analyticAt_const).pow _)
  have hl : L 0 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact pow_ne_zero _ (by simpa using (sub_ne_zero.mpr (Ne.symm (Finset.mem_filter.mp hp).2)))
  have hn : n = ∑ p ∈ A, heatIntersectionMultiplicity p := by
    unfold n S
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨x,y⟩ := p
      exact congrArg heatIntersectionMultiplicity
        (Prod.ext (Finset.mem_filter.mp hp).2.symm rfl)
    · intro p hp q hq he
      exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) he
  have hfact (w : ℂ) : projectedHeatDiscriminant C (τ+w) = w ^ n * L w := by
    rw [projectedHeatDiscriminant, ← Finset.prod_filter_mul_prod_filter_not C (fun p => p.1 = τ),
      hn, ← Finset.prod_pow_eq_pow_sum]
    apply congrArg (· * L w)
    apply Finset.prod_congr rfl
    intro p hp
    rw [(Finset.mem_filter.mp hp).2, add_sub_cancel_left]
  obtain ⟨V,hV,hv,he⟩ := heatWindow_factor τ S
  refine ⟨fun w => L w / V w, hL.div hV hv, div_ne_zero hl hv, ?_⟩
  have hv' : ∀ᶠ (s : ℂ) in 𝓝 0, V (s ^ 2) ≠ 0 :=
    (show ContinuousAt (fun s : ℂ => s ^ 2) 0 by fun_prop).tendsto.eventually
      (by simpa using hV.continuousAt.eventually_ne hv)
  filter_upwards [he,hv'] with s hs hvs
  rw [hfact, hs]
  field_simp
  ring

/-- Boundary winding of the compact marked divisor. Any holomorphic
nonvanishing change of its equation gives the same winding. -/
theorem compact_heatDiscriminant_winding (K : Set (ℂ × ℂ)) (hK : IsCompact K)
    {a b : ℂ} (inside : ∀ p ∈ K, p ∈ multipleZeros →
      a.re < p.1.re ∧ p.1.re < b.re ∧ a.im < p.1.im ∧ p.1.im < b.im) :
    ∃ C : Finset (ℂ × ℂ), (∀ p, p ∈ C ↔ p ∈ K ∧ p ∈ multipleZeros) ∧
      heatIntersectionMass K = ∑ p ∈ C, (heatIntersectionMultiplicity p : ℝ≥0∞) ∧
      rectIntegral (logDeriv (projectedHeatDiscriminant C)) a b =
        2 * Real.pi * I * ((∑ p ∈ C, heatIntersectionMultiplicity p : ℕ) : ℂ) := by
  obtain ⟨C,hC,hm⟩ := compact_heatIntersectionMass K hK
  refine ⟨C,hC,hm,?_⟩
  have h := rectIntegral_logDeriv_multi_zero C Prod.fst heatIntersectionMultiplicity
    (h := fun _ => (1 : ℂ)) (fun p hp => inside p ((hC p).mp hp).1 ((hC p).mp hp).2)
    (Set.subset_univ _) (fun _ _ => analyticAt_const) (fun _ _ => one_ne_zero)
  unfold projectedHeatDiscriminant
  simpa using h

/-! ## Two folds on the same two sheets -/

/-- The discriminant of the model `y² = (t−a)(t−b)`. -/
def twoFoldDiscriminant (a b t : ℂ) : ℂ := (t - a) * (t - b) * 4

/-- In the coordinate `u = y/(t−b)` the two-sheeted equation becomes
`u² = (t−a)/(t−b)`. The latter base coordinate has nonzero derivative
at `a`, so the local turn negates `u`. Interchanging `a,b` gives the
same negation at the other fold. -/
theorem twoFold_local_chart (a b : ℂ) (hab : a ≠ b) :
    HasDerivAt (fun t : ℂ => (t-a)/(t-b)) (a-b)⁻¹ a ∧
    ∀ t y : ℂ, t ≠ b →
      (y ^ 2 = (t-a)*(t-b) ↔ (y/(t-b)) ^ 2 = (t-a)/(t-b)) := by
  have h := ((hasDerivAt_id a).sub_const a).div ((hasDerivAt_id a).sub_const b)
    (sub_ne_zero.mpr hab)
  refine ⟨?_, ?_⟩
  · change HasDerivAt (fun t : ℂ => (t-a)/(t-b))
        ((1 * (a-b) - (a-a) * 1) / (a-b)^2) a at h
    have he : (1 * (a-b) - (a-a) * 1) / (a-b)^2 = (a-b)⁻¹ := by
      field_simp [sub_ne_zero.mpr hab]
      ring
    rwa [he] at h
  · intro t y ht
    field_simp [sub_ne_zero.mpr ht]

/-- Both turns on a regular fibre negate `y`. They cancel under composition
and interchange its two distinct points. -/
theorem twoFold_turns_on_fiber {a b t y : ℂ} (ht : t ≠ a) (ht' : t ≠ b)
    (hy : y ^ 2 = (t-a)*(t-b)) :
    ((-y) ^ 2 = (t-a)*(t-b)) ∧ -y ≠ y ∧ -(-y) = y ∧
    ∀ w : ℂ, w ^ 2 = (t-a)*(t-b) ↔ w = y ∨ w = -y := by
  have hne : y ≠ 0 := fun h => (mul_ne_zero (sub_ne_zero.mpr ht) (sub_ne_zero.mpr ht'))
    (by simpa [h] using hy.symm)
  refine ⟨by simpa only [neg_sq] using hy, ?_, neg_neg _, fun w => ?_⟩
  · intro h
    apply hne
    linear_combination -h / 2
  · rw [← hy, sq_eq_sq_iff_eq_or_eq_neg]

/-- A box isolating the first fold has winding one. Symmetry gives one
at the second fold as well. -/
theorem twoFold_winding_one {a b l u : ℂ}
    (hl : l.re < a.re) (hu : a.re < u.re) (hl' : l.im < a.im) (hu' : a.im < u.im)
    (hout : b ∉ (uIcc l.re u.re ×ℂ uIcc l.im u.im)) :
    rectIntegral (logDeriv (twoFoldDiscriminant a b)) l u = 2 * Real.pi * I := by
  have hr := rectIntegral_logDeriv_single_zero (h := fun t : ℂ => (t-b)*4)
    (ρ := a) (m := 1) hl hu hl' hu' (Set.Subset.refl _)
    (fun _ _ => (analyticAt_id.sub analyticAt_const).mul analyticAt_const)
    (fun t ht => mul_ne_zero (sub_ne_zero.mpr (fun he => hout (he ▸ ht))) (by norm_num))
  change rectIntegral (logDeriv (fun z => (z-a)*(z-b)*4)) l u = _
  simpa [mul_assoc] using hr

/-- The discriminant winding around both folds is two. -/
theorem twoFold_winding_two {a b l u : ℂ} (hab : a ≠ b)
    (hin : ∀ x ∈ ({a,b} : Finset ℂ), l.re < x.re ∧ x.re < u.re ∧
      l.im < x.im ∧ x.im < u.im) :
    rectIntegral (logDeriv (twoFoldDiscriminant a b)) l u = 2 * Real.pi * I * 2 := by
  classical
  have hr := rectIntegral_logDeriv_multi_zero ({a,b} : Finset ℂ) id (fun _ => 1)
    (h := fun _ => 4) hin (Set.subset_univ _) (fun _ _ => analyticAt_const)
    (fun _ _ => by norm_num)
  change rectIntegral (logDeriv (fun z => (z-a)*(z-b)*4)) l u = _
  simpa [hab] using hr

#print axioms IsCollision.exists_discriminant_winding
#print axioms heatIntersectionMass_cut
#print axioms realHeatWindow_vanishing_iff_rh
#print axioms heatWindowDiscriminant_winding
#print axioms projectedHeatDiscriminant_cut
#print axioms projectedHeatDiscriminant_local
#print axioms compact_heatDiscriminant_winding
#print axioms twoFold_local_chart
#print axioms twoFold_turns_on_fiber
#print axioms twoFold_winding_one
#print axioms twoFold_winding_two

end

end GaloisForLFunctions.GaloisTheoryOfZeros
