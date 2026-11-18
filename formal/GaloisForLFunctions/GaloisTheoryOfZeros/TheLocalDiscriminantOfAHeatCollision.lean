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
  have hcard := Finset.two_mul_card_image_offDiag (profileRoots m)
  rw [Finset.card_image_offDiag, card_profileRoots] at hcard
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
    rw [(collisionBranch_spec hc (heatModelFwd_profileRoot ha)).2.1,
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
  simp only [heatIntersectionMass, Set.indicator_union_of_disjoint h, Pi.add_apply, ENNReal.tsum_add]

/-- Points on a cut shared by two closed windows are counted exactly once. -/
theorem heatIntersectionMass_cut (A B : Set (ℂ × ℂ)) :
    heatIntersectionMass (A ∪ B) + heatIntersectionMass (A ∩ B) =
      heatIntersectionMass A + heatIntersectionMass B := by
  classical
  simp only [heatIntersectionMass, ← ENNReal.tsum_add]
  apply tsum_congr
  intro p
  by_cases ha : p ∈ A <;> by_cases hb : p ∈ B <;> simp [ha, hb, two_mul]

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
  · convert h using 1
    simp [sq, sub_ne_zero.mpr hab, div_eq_mul_inv, mul_assoc]
  · intro t y ht
    field_simp [sub_ne_zero.mpr ht]
    constructor <;> intro he <;> linear_combination he

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
  simpa [twoFoldDiscriminant, mul_assoc] using hr

/-- The discriminant winding around both folds is two. -/
theorem twoFold_winding_two {a b l u : ℂ} (hab : a ≠ b)
    (hin : ∀ x ∈ ({a,b} : Finset ℂ), l.re < x.re ∧ x.re < u.re ∧
      l.im < x.im ∧ x.im < u.im) :
    rectIntegral (logDeriv (twoFoldDiscriminant a b)) l u = 2 * Real.pi * I * 2 := by
  classical
  have hr := rectIntegral_logDeriv_multi_zero ({a,b} : Finset ℂ) id (fun _ => 1)
    (h := fun _ => 4) hin (Set.subset_univ _) (fun _ _ => analyticAt_const)
    (fun _ _ => by norm_num)
  simpa [twoFoldDiscriminant, hab] using hr

end

end GaloisForLFunctions.GaloisTheoryOfZeros
