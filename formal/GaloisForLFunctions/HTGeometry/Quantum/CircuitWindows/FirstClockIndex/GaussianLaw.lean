import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FirstClockIndex.PhysicalBlock
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FirstClockIndex.ClockScales
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # The first affordable positive multiple on a time-sampled Gaussian clock -/
open Set Filter MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstClockIndex
noncomputable section
open SharpOccupation

/-- The first positive affordable multiple exists and lies strictly between L and U. -/
def firstIndexBetween {n : ℕ} (H : selfAdjoint (Register n)) (j : ℕ) (ε t L U : ℝ) : Prop :=
  ∃ q : ℕ, 0 < q ∧ (q:ℝ)*t ∈ visitSet H j ε ∧ L < (q:ℝ) ∧ (q:ℝ) < U ∧
    ∀ m : ℕ, 0 < m → m < q → (m:ℝ)*t ∉ visitSet H j ε

private theorem first_of_tests {n s M : ℕ} {H : selfAdjoint (Register n)} {ε t L U : ℝ}
    (hlo : t ∉ earlyVisit H s ⌊L⌋₊ ε) (hhi : t ∈ earlyVisit H 0 M ε) (hdate : (M:ℝ) < U) :
    ∀ j ≤ s, firstIndexBetween H j ε t L U := by
  classical
  intro j hj
  obtain ⟨r,hr,hrM,z,hz,C,hC,herr⟩ := hhi
  let P (q : ℕ) := 0 < q ∧ (q:ℝ)*t ∈ visitSet H j ε
  have hr' : P r := ⟨hr,z,hz,C,hC.trans (Nat.zero_le _),herr⟩
  have hex : ∃ q, P q := ⟨r,hr'⟩
  let q := Nat.find hex
  obtain ⟨hq,hvisit⟩ : P q := Nat.find_spec hex
  refine ⟨q,hq,hvisit,?_,(Nat.cast_le.mpr ((Nat.find_min' hex hr').trans hrM)).trans_lt hdate,?_⟩
  · apply lt_of_not_ge
    intro he
    obtain ⟨v,hv,V,hV,hE⟩ := hvisit
    exact hlo ⟨q,hq,Nat.le_floor he,v,hv,V,hV.trans hj,hE⟩
  · exact fun m hm hmq hv => Nat.find_min hex hmq ⟨hm,hv⟩

private theorem bad_fraction {A B E : Set ℝ} (sub : E ⊆ A ∪ B) {a T : ℝ} (ha : a < T) :
    volume.real (E ∩ Icc a T)/(T-a) ≤
      volume.real (A ∩ Icc a T)/(T-a)+volume.real (B ∩ Icc a T)/(T-a) := by
  rw [←add_div]
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr ha.le)
  refine (measureReal_mono (inter_subset_inter_left (Icc a T) sub)
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)).trans ?_
  rw [union_inter_distrib_right]
  exact measureReal_union_le _ _

/-- For one fixed Gaussian chain, the first affordable positive multiple of a
time-sampled period has exponential rate 1/x per spectral level, simultaneously
at every subcritical budget, where x is the arc fraction at the physical error. -/
theorem gaussian_first_clock_index_rate :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℕ → ℕ, subcriticalBudget s →
      ∀ ε ∈ Ioo (0:ℝ) (Real.sqrt 2), ∀ l b : ℝ,
      0 < l → l < physicalArc ε → physicalArc ε < b → b < 1 →
      ∃ c ∈ Ioo (0:ℝ) 1, ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
          volume.real ({t | ∀ j ≤ s N, firstIndexBetween H j ε t ((1/b)^D) ((1/l)^D)}ᶜ ∩ Icc a T)/(T-a)
            < 2*c^(D-1) := by
  filter_upwards [gaussian_no_early_clock_index,gaussian_path_all_prefixes_maximally_projective] with ω hlow hω
  intro s hs ε hε l b hl hlx hxb hb
  obtain ⟨hx,htol⟩ := physicalArc_spec hε.1 hε.2
  obtain ⟨y,hxy,hyb⟩ := exists_between hxb
  obtain ⟨v,hv,hvblocks⟩ := clock_blocks hl hlx hx.2
  have hbpos := hx.1.trans hxb
  have hyr := div_pos (hx.1.trans hxy) hbpos
  have hyr1 := (div_lt_one hbpos).mpr hyb
  let c := max v (y/b)
  have hcp : 0 < c := hv.1.trans_le (le_max_left ..)
  have hc1 : c < 1 := max_lt hv.2 hyr1
  refine ⟨c,⟨hcp,hc1⟩,?_⟩
  have hg : Tendsto (fun k : ℕ => 2^(k+3)-1 : ℕ → ℕ) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro k
    change k ≤ 2^(k+3)-1
    have h : k+3 < 2^(k+3) := Nat.lt_two_pow_self
    omega
  filter_upwards [hlow s hs _ hx y b hxy hyb hb,hg.eventually hvblocks] with k hk hblock
  intro N D H a
  let d := D-1
  have hd : 1 ≤ D := pow_pos (by decide : 0 < 2) N
  have hed : d+1 = D := Nat.sub_add_cancel hd
  obtain ⟨Q,R,hQ,hR,hdate,hshort,hmass⟩ := hblock
  have hup := physical_block_bound H (hω k) hQ hR _ hx.1 hshort a (v^d) hmass
  have hdeadline : ((Q+R:ℕ):ℝ) < (1/l)^D := by
    rw [Nat.cast_add,←hed,pow_succ]
    apply hdate.trans_le
    exact le_mul_of_one_le_right (by positivity) (one_le_div hl |>.mpr (by linarith only [hlx,hx.2]))
  rw [←htol]
  filter_upwards [hk a,hup,eventually_gt_atTop a] with T hearly hlate hT
  have hbad := bad_fraction (A := earlyVisit H (s N) ⌊(1/b)^D⌋₊ (zeroGateArcTolerance _))
    (B := (earlyVisit H 0 (Q+R) (zeroGateArcTolerance _))ᶜ)
    (E := {t | ∀ j ≤ s N, firstIndexBetween H j (zeroGateArcTolerance _) t ((1/b)^D) ((1/l)^D)}ᶜ)
    (fun t ht => by
      by_cases hlo : t ∈ earlyVisit H (s N) ⌊(1/b)^D⌋₊ (zeroGateArcTolerance (physicalArc ε))
      · exact Or.inl hlo
      · exact Or.inr fun hh => ht (first_of_tests hlo hh hdeadline)) hT
  apply (hbad.trans_lt (add_lt_add_of_le_of_lt hearly (hlate 0))).trans_le
  have hu : (y/b)^D ≤ c^d := by
    rw [←hed,pow_succ]
    exact (mul_le_of_le_one_right (pow_nonneg hyr.le _) hyr1.le).trans
      (pow_le_pow_left₀ hyr.le (le_max_right ..) _)
  linarith only [hu,pow_le_pow_left₀ hv.1.le (le_max_left v (y/b)) d]

#print axioms gaussian_first_clock_index_rate
end
end GaloisForLFunctions.HTGeometry.FirstClockIndex
