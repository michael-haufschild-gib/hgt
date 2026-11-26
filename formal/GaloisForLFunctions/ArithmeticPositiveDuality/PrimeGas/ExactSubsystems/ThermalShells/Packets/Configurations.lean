import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Windows
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.PairResolution

/-! # Reading the prime packets in the physical count-one occupation sector -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets

open Real Filter Topology Set _root_.RHTower
open BinaryOrientation.LargestPrime.Bands BinaryOrientation.LargestPrime.Bands.Marks
open BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints

variable {S : Finset Nat.Primes}

private def occupied (R : BreadthSubset 1 ↥S) : ↥S := (Finset.card_eq_one.mp R.property).choose

private theorem occupation (R : BreadthSubset 1 ↥S) : R.val = {occupied R} :=
  (Finset.card_eq_one.mp R.property).choose_spec

/-- Prime label of the unique occupied mode. -/
def label (R : BreadthSubset 1 ↥S) : ℕ := (occupied R).val.val

theorem label_energy (R : BreadthSubset 1 ↥S) : energyOf R = log (label R:ℝ) := by
  simp only [energyOf,occupation R,Finset.sum_singleton]
  rfl

theorem label_injective (S : Finset Nat.Primes) : Function.Injective (label (S := S)) := by
  intro R T he
  apply energyOf_injective S 1
  rw [label_energy,label_energy,he]

theorem label_oneMode (p : ↥S) : label (oneMode p) = p.val.val := by
  have hh : ({p} : Finset ↥S) = {occupied (oneMode p)} := occupation (oneMode p)
  exact congrArg (fun x : ↥S => x.val.val) (Finset.singleton_inj.mp hh).symm

/-- Selection by prime label inside the actual one-particle sector. -/
def selected (S : Finset Nat.Primes) (P : Finset ℕ) : Finset (BreadthSubset 1 ↥S) :=
  Finset.univ.filter fun R => label R ∈ P

private theorem selected_image (P : Finset ℕ)
    (hP : ∀ p ∈ P, ∃ q : ↥S, q.val.val = p) : (selected S P).image label = P := by
  ext p
  constructor
  · rintro hp
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp hR).2
  · intro hp
    obtain ⟨q,rfl⟩ := hP p hp
    exact Finset.mem_image.mpr ⟨oneMode q,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(label_oneMode q).symm ▸ hp⟩,label_oneMode q⟩

theorem sub_selected_image {P Q : Finset ℕ} (hQ : Q ⊆ P)
    (hP : (selected S P).image label = P) : (selected S Q).image label = Q := by
  apply selected_image
  intro p hp
  obtain ⟨R,_,he⟩ := Finset.mem_image.mp (hP.symm ▸ hQ hp)
  exact ⟨occupied R,he⟩

/-- Conditional Born probabilities are the translated prime Gibbs probabilities under the label map. -/
theorem recode_share (b t : ℝ) (U A : Finset (BreadthSubset 1 ↥S)) :
    share (born b) U A = share (shifted b t) (U.image label) (A.image label) := by
  have hs (R : BreadthSubset 1 ↥S) : shifted b t (label R) = weight b energyOf R*exp (b*t) := by
    rw [shifted,weight,label_energy,← exp_add]; congr 1; ring
  rw [born_share]
  simp only [share,mass,Finset.sum_image (label_injective S).injOn,hs,← Finset.sum_mul,
    mul_div_mul_right _ _ (exp_pos (b*t)).ne']

theorem recode_variation (β γ t : ℝ) (U : Finset (BreadthSubset 1 ↥S)) :
    variation (born β) (born γ) U = variation (shifted β t) (shifted γ t) (U.image label) := by
  apply le_antisymm
  · apply variation_le
    intro A ha
    rw [recode_share β t,recode_share γ t]
    exact event_le_variation _ _ (Finset.image_subset_image ha)
  · apply variation_le
    intro A ha
    have h := Finset.mem_powerset.mpr ha
    rw [Finset.powerset_image] at h
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp h
    rw [← recode_share,← recode_share]
    exact event_le_variation _ _ (Finset.mem_powerset.mp hB)

def physical (c d D k : ℝ) (h : Ioi (0:ℝ)) := selected (added c d h) (both D k (c/h.val))

theorem translation_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun h : Ioi (0:ℝ) => c/h.val) criticalApproach atTop := by
  have hv : Tendsto (Subtype.val : Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) := tendsto_comap
  simpa only [div_eq_mul_inv,Function.comp_apply] using (tendsto_inv_nhdsGT_zero.comp hv).const_mul_atTop hc

/-- Both endpoint packets fit into every sufficiently far moving band and have total energy span ≤ D. -/
theorem physical_window {c d D k : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k) :
    ∀ᶠ h in criticalApproach, let U := physical c d D k h
      U.image label = both D k (c/h.val) ∧ U.Nonempty ∧
      ∀ x ∈ U, ∀ y ∈ U, |energyOf x-energyOf y| ≤ D := by
  have hv : Tendsto (Subtype.val : Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) := tendsto_comap
  have hsmall := (hv.mono_right nhdsWithin_le_nhds).mul_const D
  rw [zero_mul] at hsmall
  filter_upwards [(translation_limit hc).eventually (windows hD hk),
    hsmall.eventually_lt_const (sub_pos.mpr hcd)] with h hw hs
  let t := c/h.val
  have hh : 0 < h.val := h.property
  have he : h.val*t = c := by dsimp [t]; field_simp
  have represented (p : ℕ) (hp : p ∈ both D k t) : ∃ q : ↥(added c d h), q.val.val = p := by
    obtain ⟨hP,hl,hu⟩ := hw.2.2.2 p hp
    let q : Nat.Primes := ⟨p,hP⟩
    refine ⟨⟨q,(mem_added c d h q).mpr ?_⟩,rfl⟩
    change c < h.val*log (p:ℝ) ∧ h.val*log (p:ℝ) ≤ d
    have h₁ := mul_lt_mul_of_pos_left hl hh
    have h₂ := mul_le_mul_of_nonneg_left hu hh.le
    change h.val*t < _ at h₁
    change _ ≤ h.val*(t+D) at h₂
    rw [he] at h₁
    rw [mul_add,he] at h₂
    exact ⟨h₁,by linarith only [h₂,hs]⟩
  have image_eq := selected_image (both D k t) represented
  let U := physical c d D k h
  have him : U.image label = both D k t := image_eq
  have hn : (U.image label).Nonempty := him.symm ▸ hw.1.mono Finset.subset_union_left
  refine ⟨him,Finset.image_nonempty.mp hn,?_⟩
  intro x hx y hy
  have loc (z) (hz : z ∈ U) := (hw.2.2.2 (label z) (him ▸ Finset.mem_image_of_mem label hz)).2
  rw [label_energy,label_energy]
  exact abs_le.mpr ⟨by linarith only [(loc x hx).1,(loc y hy).2],by linarith only [(loc y hy).1,(loc x hx).2]⟩

#print axioms recode_share
#print axioms recode_variation
#print axioms physical_window

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets
