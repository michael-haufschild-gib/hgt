import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Grid cancellation forces many zeros

A continuous real function whose absolute mass on an interval exceeds the total cancellation of
its integrals over a uniform grid must vanish in many grid cells.  This is the sharp combinatorial
device behind every sign-change count for Hardy's function: on a cell without an interior zero the
function has constant sign, so its absolute mass equals the modulus of its signed integral, and the
whole surplus of absolute mass over the summed cancellation is carried by the cells that do contain
a zero.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-! ## Constant sign on a cell without interior zeros -/

/-- A continuous real function without interior zeros has constant strict sign there. -/
theorem sign_constant_of_no_interior_zero {f : ℝ → ℝ} {u v : ℝ}
    (hf : ContinuousOn f (Icc u v)) (hno : ∀ x ∈ Ioo u v, f x ≠ 0) :
    (∀ x ∈ Ioo u v, 0 < f x) ∨ (∀ x ∈ Ioo u v, f x < 0) := by
  by_cases hempty : (Ioo u v).Nonempty
  · obtain ⟨m, hm⟩ := hempty
    have hsub : ∀ x ∈ Ioo u v, ∀ y ∈ Ioo u v, uIcc x y ⊆ Ioo u v := by
      intro x hx y hy
      rw [uIcc_eq_union]
      refine union_subset (Icc_subset_Ioo ?_ ?_) (Icc_subset_Ioo ?_ ?_)
      · exact hx.1
      · exact hy.2
      · exact hy.1
      · exact hx.2
    have hkey : ∀ x ∈ Ioo u v, ∀ y ∈ Ioo u v, 0 < f x → 0 < f y := by
      intro x hx y hy hfx
      by_contra hfy
      have hneg : f y < 0 := lt_of_le_of_ne (not_lt.mp hfy) (hno y hy)
      have hcont : ContinuousOn f (uIcc x y) :=
        hf.mono ((hsub x hx y hy).trans Ioo_subset_Icc_self)
      have hmem : (0 : ℝ) ∈ uIcc (f x) (f y) := by
        rw [uIcc_eq_union]
        exact Or.inr ⟨hneg.le, hfx.le⟩
      obtain ⟨z, hz, hfz⟩ := intermediate_value_uIcc hcont hmem
      exact hno z (hsub x hx y hy hz) hfz
    rcases lt_or_gt_of_ne (hno m hm) with hneg | hpos
    · refine Or.inr fun y hy => ?_
      by_contra hcon
      have hposy : 0 < f y := lt_of_le_of_ne (not_lt.mp hcon) (Ne.symm (hno y hy))
      exact absurd (hkey y hy m hm hposy) (not_lt.mpr hneg.le)
    · exact Or.inl fun y hy => hkey m hm y hy hpos
  · rw [not_nonempty_iff_eq_empty] at hempty
    exact Or.inl fun x hx => absurd hx (by rw [hempty]; exact fun h => h)

/-! ## Absolute mass equals cancellation on a cell without interior zeros -/

theorem ae_ne_singleton (v : ℝ) : ∀ᵐ x : ℝ, x ≠ v := by
  rw [MeasureTheory.ae_iff]
  have : {x : ℝ | ¬ x ≠ v} = {v} := by
    ext x; simp
  rw [this]
  exact MeasureTheory.measure_singleton v

/-- On a cell without interior zeros the absolute mass is the modulus of the signed integral. -/
theorem integral_abs_le_abs_integral_of_no_interior_zero {f : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (hf : ContinuousOn f (Icc u v)) (hno : ∀ x ∈ Ioo u v, f x ≠ 0) :
    (∫ t in u..v, |f t|) ≤ |∫ t in u..v, f t| := by
  have hint : IntervalIntegrable f volume u v := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le huv]
  have habs : IntervalIntegrable (fun t => |f t|) volume u v := hint.abs
  rcases sign_constant_of_no_interior_zero hf hno with hpos | hneg
  · have heq : (∫ t in u..v, |f t|) = ∫ t in u..v, f t := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [ae_ne_singleton v] with x hx hxmem
      rw [Set.uIoc_of_le huv] at hxmem
      have hxo : x ∈ Ioo u v := ⟨hxmem.1, lt_of_le_of_ne hxmem.2 hx⟩
      exact abs_of_pos (hpos x hxo)
    rw [heq]
    exact le_abs_self _
  · have heq : (∫ t in u..v, |f t|) = -∫ t in u..v, f t := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [ae_ne_singleton v] with x hx hxmem
      rw [Set.uIoc_of_le huv] at hxmem
      have hxo : x ∈ Ioo u v := ⟨hxmem.1, lt_of_le_of_ne hxmem.2 hx⟩
      exact abs_of_neg (hneg x hxo)
    rw [heq]
    exact neg_le_abs _

/-- **The cancellation atom.**  Strictly more absolute mass than cancellation forces an interior
zero. -/
theorem exists_zero_of_abs_integral_lt {f : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (hf : ContinuousOn f (Icc u v))
    (h : |∫ t in u..v, f t| < ∫ t in u..v, |f t|) :
    ∃ x ∈ Ioo u v, f x = 0 := by
  by_contra hcon
  have hno : ∀ x ∈ Ioo u v, f x ≠ 0 := by
    intro x hx hfx
    exact hcon ⟨x, hx, hfx⟩
  exact absurd (integral_abs_le_abs_integral_of_no_interior_zero huv hf hno) (not_le.mpr h)

/-! ## The grid count -/

/-- **Grid cancellation zero count.**  If the absolute mass of `f` on `[a, a + N H]` exceeds the
total cancellation `Bsum` of its signed integrals over the uniform grid of mesh `H`, then `f` has
at least `(L - Bsum) / Mx` distinct interior zeros, where `Mx` bounds the absolute mass carried by
a single cell. -/
theorem exists_finset_zeros_card_mul_ge {f : ℝ → ℝ} {a H : ℝ} {N : ℕ} {L Bsum Mx : ℝ}
    (hH : 0 < H) (hf : ContinuousOn f (Icc a (a + (N : ℝ) * H)))
    (hL : L ≤ ∫ t in a..(a + (N : ℝ) * H), |f t|)
    (hB : ∑ j ∈ Finset.range N,
        |∫ t in (a + (j : ℝ) * H)..(a + ((j : ℝ) + 1) * H), f t| ≤ Bsum)
    (hMx : ∀ j ∈ Finset.range N,
        (∫ t in (a + (j : ℝ) * H)..(a + ((j : ℝ) + 1) * H), |f t|) ≤ Mx) :
    ∃ Zs : Finset ℝ, (∀ x ∈ Zs, x ∈ Ioo a (a + (N : ℝ) * H) ∧ f x = 0) ∧
      L - Bsum ≤ (Zs.card : ℝ) * Mx := by
  classical
  obtain ⟨g, hgeq⟩ : ∃ g : ℕ → ℝ, ∀ j : ℕ, g j = a + (j : ℝ) * H := ⟨_, fun _ => rfl⟩
  have hgsucc : ∀ j : ℕ, g (j + 1) = a + ((j : ℝ) + 1) * H := by
    intro j
    rw [hgeq]
    push_cast
    ring
  have hgmono : ∀ {i j : ℕ}, i ≤ j → g i ≤ g j := by
    intro i j hij
    have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    rw [hgeq, hgeq]
    nlinarith [hH.le]
  have hg0 : g 0 = a := by rw [hgeq]; norm_num
  have hgN : g N = a + (N : ℝ) * H := hgeq N
  have hcontj : ∀ j : ℕ, j < N → ContinuousOn f (Icc (g j) (g (j + 1))) := by
    intro j hj
    refine hf.mono (Icc_subset_Icc ?_ ?_)
    · rw [← hg0]; exact hgmono (Nat.zero_le j)
    · rw [← hgN]; exact hgmono (by omega)
  have hintabs : ∀ j : ℕ, j < N →
      IntervalIntegrable (fun t => |f t|) volume (g j) (g (j + 1)) := by
    intro j hj
    refine IntervalIntegrable.abs ?_
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (hgmono (by omega : j ≤ j + 1))]
    exact hcontj j hj
  have hsum : ∑ j ∈ Finset.range N, (∫ t in (g j)..(g (j + 1)), |f t|)
      = ∫ t in a..(a + (N : ℝ) * H), |f t| := by
    rw [intervalIntegral.sum_integral_adjacent_intervals hintabs, hg0, hgN]
  set S : Finset ℕ := (Finset.range N).filter
    (fun j => |∫ t in (g j)..(g (j + 1)), f t| < ∫ t in (g j)..(g (j + 1)), |f t|) with hSdef
  have hex : ∀ j : ℕ, ∃ x : ℝ, j ∈ S → (x ∈ Ioo (g j) (g (j + 1)) ∧ f x = 0) := by
    intro j
    by_cases hj : j ∈ S
    · obtain ⟨hjr, hjlt⟩ := Finset.mem_filter.mp hj
      obtain ⟨x, hx, hfx⟩ := exists_zero_of_abs_integral_lt
        (hgmono (by omega : j ≤ j + 1)) (hcontj j (Finset.mem_range.mp hjr)) hjlt
      exact ⟨x, fun _ => ⟨hx, hfx⟩⟩
    · exact ⟨a, fun hc => absurd hc hj⟩
  choose φ hφ using hex
  have hinj : Set.InjOn φ (S : Set ℕ) := by
    intro i hi j hj hij
    by_contra hne
    have hPi := hφ i (Finset.mem_coe.mp hi)
    have hPj := hφ j (Finset.mem_coe.mp hj)
    rcases Nat.lt_or_ge i j with hlt | hge
    · have hstep : g (i + 1) ≤ g j := hgmono (by omega)
      have h1 : φ i < g (i + 1) := hPi.1.2
      have h2 : g j < φ j := hPj.1.1
      rw [hij] at h1
      linarith
    · have hlt : j < i := by omega
      have hstep : g (j + 1) ≤ g i := hgmono (by omega)
      have h1 : φ j < g (j + 1) := hPj.1.2
      have h2 : g i < φ i := hPi.1.1
      rw [hij] at h2
      linarith
  refine ⟨S.image φ, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hjr, -⟩ := Finset.mem_filter.mp hj
    have hjN : j < N := Finset.mem_range.mp hjr
    obtain ⟨hmem, hfz⟩ := hφ j hj
    refine ⟨Ioo_subset_Ioo ?_ ?_ hmem, hfz⟩
    · rw [← hg0]; exact hgmono (Nat.zero_le j)
    · rw [← hgN]; exact hgmono (by omega : j + 1 ≤ N)
  · rw [Finset.card_image_of_injOn hinj]
    have hSbound : ∑ j ∈ S, (∫ t in (g j)..(g (j + 1)), |f t|) ≤ (S.card : ℝ) * Mx := by
      have hb : ∀ j ∈ S, (∫ t in (g j)..(g (j + 1)), |f t|) ≤ Mx := by
        intro j hj
        obtain ⟨hjr, -⟩ := Finset.mem_filter.mp hj
        rw [hgeq j, hgsucc j]
        exact hMx j hjr
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul S _ Mx hb
    have hrest : ∑ j ∈ (Finset.range N).filter (fun j =>
        ¬ (|∫ t in (g j)..(g (j + 1)), f t| < ∫ t in (g j)..(g (j + 1)), |f t|)),
        (∫ t in (g j)..(g (j + 1)), |f t|) ≤ Bsum := by
      have h1 : ∀ j ∈ (Finset.range N).filter (fun j =>
          ¬ (|∫ t in (g j)..(g (j + 1)), f t| < ∫ t in (g j)..(g (j + 1)), |f t|)),
          (∫ t in (g j)..(g (j + 1)), |f t|) ≤ |∫ t in (g j)..(g (j + 1)), f t| := by
        intro j hj
        exact not_lt.mp (Finset.mem_filter.mp hj).2
      have h2 := Finset.sum_le_sum h1
      have h3 : ∑ j ∈ (Finset.range N).filter (fun j =>
          ¬ (|∫ t in (g j)..(g (j + 1)), f t| < ∫ t in (g j)..(g (j + 1)), |f t|)),
          |∫ t in (g j)..(g (j + 1)), f t|
          ≤ ∑ j ∈ Finset.range N, |∫ t in (g j)..(g (j + 1)), f t| := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro j _ _
        exact abs_nonneg _
      have h4 : ∑ j ∈ Finset.range N, |∫ t in (g j)..(g (j + 1)), f t| ≤ Bsum := by
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_)) hB
        rw [hgeq j, hgsucc j]
      linarith
    have hsplit : ∑ j ∈ Finset.range N, (∫ t in (g j)..(g (j + 1)), |f t|)
        = (∑ j ∈ S, ∫ t in (g j)..(g (j + 1)), |f t|)
          + ∑ j ∈ (Finset.range N).filter (fun j =>
              ¬ (|∫ t in (g j)..(g (j + 1)), f t| < ∫ t in (g j)..(g (j + 1)), |f t|)),
              ∫ t in (g j)..(g (j + 1)), |f t| := by
      rw [hSdef]
      exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hgoal : L ≤ (S.card : ℝ) * Mx + Bsum := by
      calc L ≤ ∫ t in a..(a + (N : ℝ) * H), |f t| := hL
        _ = ∑ j ∈ Finset.range N, (∫ t in (g j)..(g (j + 1)), |f t|) := hsum.symm
        _ ≤ (S.card : ℝ) * Mx + Bsum := by rw [hsplit]; exact add_le_add hSbound hrest
    linarith

end GaloisForLFunctions.HTGeometry
