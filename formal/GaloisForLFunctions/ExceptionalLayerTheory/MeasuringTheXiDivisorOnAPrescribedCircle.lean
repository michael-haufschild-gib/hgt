import GaloisForLFunctions.ExceptionalLayerTheory.TheHighDerivativeAreasOfAWholeObservationDisk

/-!
# Measuring zeros on a prescribed circle

Every sufficiently thin symmetric annulus about a prescribed circle has
regular boundary and contains exactly the zeros on that circle. The jump
in winding measures their total multiplicity. Differences of derivative
areas give every fractional moment of their orders. The prescribed
circle itself may pass through zeros.
-/
noncomputable section
open Complex Filter Metric Set Topology RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem isolated_zero_radius (c : ℂ) {R : ℝ} (hR : 0<R) :
    ∃ ε : ℝ, 0<ε ∧ ε≤R ∧ ∀ d : ℝ, 0<d → d<ε → ∀ z : ℂ, xi z=0 →
      R-d≤‖z-c‖ → ‖z-c‖≤R+d → ‖z-c‖=R := by
  let Z : Set ℂ := {z ∈ closedBall c (R+1) | xi z=0}
  let B := ((fun z : ℂ => ‖z-c‖) '' Z) \ {R}
  have hfinite : B.Finite := ((xi_zeros_closedBall_finite c (R+1)).image
    (fun z : ℂ => ‖z-c‖)).subset sdiff_subset
  have hnb : R∈Bᶜ := fun h => h.2 rfl
  obtain ⟨r,hr,hrB⟩ := Metric.mem_nhds_iff.mp (hfinite.isClosed.isOpen_compl.mem_nhds hnb)
  refine ⟨min R (min 1 r),lt_min hR (lt_min zero_lt_one hr),min_le_left ..,?_⟩
  intro d hd hd' z hz h₁ h₂
  have hdr : d<r := (hd'.trans_le (min_le_right ..)).trans_le (min_le_right ..)
  have hd1 : d<1 := (hd'.trans_le (min_le_right ..)).trans_le (min_le_left ..)
  have hin : ‖z-c‖∈ball R r := by
    rw [mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith only [h₁,h₂,hdr]
  by_contra hn
  exact hrB hin ⟨⟨z,⟨mem_closedBall.mpr (by rw [dist_eq_norm]; linarith only [h₂,hd1]),hz⟩,rfl⟩,hn⟩

/-- A common collar and a common exact boundary divisor work at every
derivative order and every sufficiently small positive annulus width. -/
theorem xi_circle_divisor_from_annular_areas (c : ℂ) {R : ℝ} (hR : 0<R) :
    ∃ S : Finset ℂ, (∀ z, z∈S ↔ ‖z-c‖=R ∧ xi z=0) ∧
    ∃ ε : ℝ, 0<ε ∧ ∀ d : ℝ, 0<d → d<ε →
      (windingNumber (fun θ => xi (c+↑(R+d)*exp (I*↑θ))) 0 (2*Real.pi) -
       windingNumber (fun θ => xi (c+↑(R-d)*exp (I*↑θ))) 0 (2*Real.pi) =
       ∑ z ∈ S, (hadamardOrder z:ℤ)) ∧
      ∀ j : ℕ, Tendsto (fun u => xiDerivativeDiskArea j c (R+d) u-xiDerivativeDiskArea j c (R-d) u)
        atTop (𝓝 (∑ z ∈ S, (hadamardOrder z:ℝ)^(2/((j+1:ℕ):ℝ)))) := by
  classical
  let S := (xi_zeros_closedBall_finite c R).toFinset.filter (fun z => ‖z-c‖=R)
  have hS (z : ℂ) : z∈S ↔ ‖z-c‖=R ∧ xi z=0 := by
    change z∈Finset.filter _ _ ↔ _
    rw [Finset.mem_filter,Set.Finite.mem_toFinset]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨mem_closedBall.mpr (by rw [dist_eq_norm,h.1]),h.2⟩,h.1⟩⟩
  obtain ⟨ε,hε,hεR,hgap⟩ := isolated_zero_radius c hR
  refine ⟨S,hS,ε,hε,?_⟩
  intro d hd hde
  have hlow := sub_pos.mpr (hde.trans_le hεR)
  have hgap' := hgap d hd hde
  have hlo (z : ℂ) (hz : ‖z-c‖=R-d) (hz0 : xi z=0) : False := by
    have h := hgap' z hz0 hz.ge (by linarith only [hz,hd])
    linarith only [h,hz,hd]
  have hhi (z : ℂ) (hz : ‖z-c‖=R+d) (hz0 : xi z=0) : False := by
    have h := hgap' z hz0 (by linarith only [hz,hd]) hz.le
    linarith only [h,hz,hd]
  obtain ⟨A,hA,hwA,ha⟩ := xi_disk_fractional_moments c hlow hlo
  obtain ⟨B,hB,hwB,hb⟩ := xi_disk_fractional_moments c (add_pos hR hd) hhi
  have hdis : Disjoint A S := Finset.disjoint_left.mpr (fun z hz hs => by
    have h₁ := ((hA z).mp hz).1
    have h₂ := ((hS z).mp hs).1
    linarith only [h₁,h₂,hd])
  have he : B=A∪S := by
    ext z
    rw [hB,Finset.mem_union,hA,hS]
    constructor
    · rintro ⟨hz,hz0⟩
      by_cases h : ‖z-c‖<R-d
      · exact Or.inl ⟨h,hz0⟩
      · exact Or.inr ⟨hgap' z hz0 (le_of_not_gt h) hz.le,hz0⟩
    · rintro (⟨h,hz⟩|⟨h,hz⟩)
      · exact ⟨by linarith only [h,hd],hz⟩
      · exact ⟨by linarith only [h,hd],hz⟩
  constructor
  · rw [hwB,hwA,he,Finset.sum_union hdis,add_sub_cancel_left]
  · intro j
    have h := (hb j).sub (ha j)
    rwa [he,Finset.sum_union hdis,add_sub_cancel_left] at h

#print axioms xi_circle_divisor_from_annular_areas
end GaloisForLFunctions.ExceptionalLayerTheory
