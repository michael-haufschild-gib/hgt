import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.CircuitWindows.PairPacking
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.ForwardWindow

/-! # Charging forward circuit hits to unit-separated return records -/
open Real Set MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.CircuitWindows
open EmptyVisitFlux SharpOccupation Depth
noncomputable section

private theorem covered {F : Set ℝ} {a : ℝ} (t : ℕ→ℝ) (h₀ : t 0=a)
    (ht : ∀ j, IsLeast {v | t j+1≤v ∧ v∈F} (t (j+1)))
    {w : ℝ} (hw : w∈F) (haw : a≤w) (n : ℕ) (hn : w≤t n) :
    ∃ j≤n, w∈Icc (t j) (t j+1) := by
  induction n with
  | zero =>
    exact ⟨0,le_rfl,by rwa [h₀],hn.trans (le_add_of_nonneg_right zero_le_one)⟩
  | succ n ih =>
    rcases eq_or_lt_of_le hn with he|he
    · exact ⟨n+1,le_rfl,he.ge,he.le.trans (le_add_of_nonneg_right zero_le_one)⟩
    by_cases h : w≤t n
    · obtain ⟨j,hj,hh⟩ := ih h
      exact ⟨j,hj.trans (Nat.le_succ _),hh⟩
    · exact ⟨n,Nat.le_succ _,(le_of_not_ge h),
        (lt_of_not_ge (fun hl => he.not_ge ((ht n).2 ⟨hl,hw⟩))).le⟩

/-- An inner visit is covered by a
unit interval following a greedy record; each such interval can serve
only the outer entries in its W-unit lookback. -/
theorem fraction_from_records {I : Type*} [Fintype I] (E : I→ℝ) (x a W rate c : ℝ)
    (hW : 0≤W) (hrate : 0<rate) (hc : 0<c) (F : Set ℝ) (t : ℕ→ℝ) (h₀ : t 0=a)
    (ht : ∀ j, IsLeast {v | t j+1≤v ∧ v∈F} (t (j+1)))
    (hmean : ∀ᶠ j : ℕ in atTop, 1/c<(t j-a)/j)
    (hafter : ∀ T u, u∈entriesAfter E x a T → a≤u ∧ u≤T)
    (hA : Tendsto (fun T : ℝ => ((entriesAfter E x a T).card:ℝ)/(T-a)) atTop (𝓝 rate)) :
    let B := (Fintype.card I:ℝ)^2+(W+1)*pairTurnRate E
    ∀ b : ℝ, c*B/rate<b → ∀ᶠ T : ℝ in atTop,
      let A := entriesAfter E x a T
      ((followed A F W).card:ℝ)/(A.card:ℝ)<b := by
  classical
  intro B b hb
  have hB : 0≤B := add_nonneg (sq_nonneg _) (mul_nonneg (by linarith only [hW])
    (Finset.sum_nonneg fun p _ => div_nonneg (le_max_left _ _) (by positivity)))
  have hT : Tendsto (fun T : ℝ => T-a) atTop atTop := by
    simpa only [id_eq,sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-a) tendsto_id
  let n (T : ℝ) := ⌊c*(T+W-a)⌋₊+1
  have hdate : Tendsto (fun T : ℝ => T+W-a) atTop atTop := by
    simpa only [id_eq,sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-a)
      (tendsto_atTop_add_const_right atTop W tendsto_id)
  have htop : Tendsto n atTop atTop := (tendsto_add_atTop_nat 1).comp
    (tendsto_nat_floor_atTop.comp (hdate.const_mul_atTop hc))
  have hnum := ((hT.const_div_atTop (c*W+2)).const_add c).mul_const B
  rw [add_zero] at hnum
  have hq := hnum.div hA hrate.ne'
  filter_upwards [htop.eventually hmean,hq.eventually_lt_const hb,eventually_gt_atTop a] with T hm hq haT
  let A := entriesAfter E x a T
  let S (j : ℕ) := A.filter fun u => u∈Icc (t j-W) (t j+1)
  have harg : 0≤c*(T+W-a) := mul_nonneg hc.le (by linarith only [haT,hW])
  have hn : 0<(n T:ℝ) := by dsimp only [n]; positivity
  have hg : T+W<t (n T) := by
    have h1 := (div_lt_div_iff₀ hc hn).mp hm
    have h2 : c*(T+W-a)<(n T:ℝ) := by simpa only [n,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (c*(T+W-a))
    change (1:ℝ)*(n T:ℝ)<(t (n T)-a)*c at h1
    apply (mul_lt_mul_iff_right₀ hc).mp
    linarith only [h1,h2]
  have hs : followed A F W ⊆ (Finset.range (n T+1)).biUnion S := by
    intro u hu
    obtain ⟨hu,w,hw,hwF⟩ := Finset.mem_filter.mp hu
    obtain ⟨hau,huT⟩ := hafter T u hu
    obtain ⟨j,hj,hjw⟩ := covered t h₀ ht hwF (hau.trans hw.1) (n T)
      ((hw.2.trans (add_le_add huT (le_refl W))).trans hg.le)
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr (Nat.lt_succ_of_le hj),
      Finset.mem_filter.mpr ⟨hu,(show u∈Icc (t j-W) (t j+1) from
        ⟨by linarith only [hw.2,hjw.1],hw.1.trans hjw.2⟩)⟩⟩
  have hS (j : ℕ) : ((S j).card:ℝ)≤B := by
    have h := entry_window_count E x a T (t j-W) (t j+1) (by linarith only [hW])
    rwa [show t j+1-(t j-W)=W+1 by ring] at h
  have hcard : ((followed A F W).card:ℝ)≤(c*(T+W-a)+2)*B := by
    calc
      _ ≤ ∑ j∈Finset.range (n T+1), ((S j).card:ℝ) := by
        exact_mod_cast (Finset.card_le_card hs).trans Finset.card_biUnion_le
      _ ≤ ∑ _j∈Finset.range (n T+1), B := Finset.sum_le_sum fun j _ => hS j
      _ ≤ _ := by
        rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ hB
        dsimp only [n]
        push_cast
        linarith only [Nat.floor_le harg]
  change (c+(c*W+2)/(T-a))*B/((A.card:ℝ)/(T-a))<b at hq
  have he : (c+(c*W+2)/(T-a))*B/((A.card:ℝ)/(T-a))=
      (c*(T+W-a)+2)*B/(A.card:ℝ) := by
    rw [div_div_eq_mul_div]
    congr 1
    field_simp [(sub_pos.mpr haT).ne']
    ring
  rw [he] at hq
  exact (div_le_div_of_nonneg_right hcard (Nat.cast_nonneg _)).trans_lt hq

end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.CircuitWindows
