import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.ExtremeClock.PhysicalFrequency
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.ExtremeClock.ResidenceCount

/-! # The tolerance-independent atom of maximum residence among actual entries -/
open Filter MeasureTheory Real Set
open scoped Topology Classical
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
open SharpOccupation ReturnSpacing.PhysicalComponents ReturnSpacing.PhysicalComponents.Depth
noncomputable section

/-- At the first near-Hilbert crossing the proportion of fresh scalar entries
lasting the maximum possible duration has an exact positive limit. Its value
depends only on the spectrum, simultaneously for every subsemicircle tolerance. -/
theorem gaussian_maximum_entry_atom :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let E := fun i => -H.2.isHermitian.eigenvalues i
      let w := fun i => E i/(2*π)
      ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧ (∀ t∈Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        ∃ p q, ∃ he : w q < w p, (∀ i, w q≤w i ∧ w i≤w p) ∧
          let W := w p-w q
          let θ := fun i => (w i-w q)/W
          let b : {i // i≠q} := ⟨p,fun h => he.ne (congrArg w h.symm)⟩
          let A := W*(∏ i : {j : {i // i≠q} // j≠b}, 2*min (θ i.val.val) (1-θ i.val.val))/pairTurnRate E
          0 < A ∧ ∀ ε∈Ioo (0:ℝ) (sqrt 2), let r := physicalArc ε
            let F := entriesAfter E r σ
            Tendsto (fun T : ℝ => ((longVisits (visitSet H 0 ε) (2*r/W) (F T)).card:ℝ)/(F T).card)
              atTop (𝓝 A) := by
  filter_upwards [gaussian_maximum_cell_frequency,gaussian_empty_visit_flux,
    gaussian_path_all_prefixes_maximally_projective] with ω hf hflux hi
  filter_upwards [hf] with k hk
  intro N H P E w
  obtain ⟨σ,hσ,hc,hb,p,q,he,hspan,hclock⟩ := hk
  refine ⟨σ,hσ,hc,hb,p,q,he,hspan,?_⟩
  intro W θ b A
  let J := {i : Fin N→Bool // i≠q}
  let K := {j : J // j≠b}
  let f (i : K) := 2*min (θ i.val.val) (1-θ i.val.val)
  have hW : 0<W := sub_pos.mpr he
  have hR := pair_rate_pos E (maximallyProjectiveEnergy_neg (hi k))
  have hcard : Fintype.card K=2^N-2 := by
    have hj : Fintype.card J=2^N-1 := by simp [J,Fintype.card_subtype_compl]
    have hk : Fintype.card K=Fintype.card J-1 := by simp [K,Fintype.card_subtype_compl]
    omega
  have product (r : ℝ) : (∏ i : K, 2*(r*min (θ i.val.val) (1-θ i.val.val))) =
      r^(2^N-2)*∏ i : K, f i := by
    simp only [show (fun i : K => 2*(r*min (θ i.val.val) (1-θ i.val.val)))=(fun i : K => r*f i)
      from funext fun _ => by dsimp only [f]; ring, Finset.prod_mul_distrib,
      Finset.prod_const,Finset.card_univ,hcard]
  have oneTol : (1:ℝ)∈Ioo (0:ℝ) (sqrt 2) := ⟨zero_lt_one,(lt_sqrt zero_le_one).mpr (by norm_num)⟩
  have hpos := (hclock 1 oneTol).1
  rw [product] at hpos
  have hp := pos_of_mul_pos_right hpos (pow_nonneg (physicalArc_spec oneTol.1 oneTol.2).1.1.le _)
  refine ⟨div_pos (mul_pos hW hp) hR,?_⟩
  intro ε hε r F
  let S := visitSet H 0 ε
  let shift := ⌊σ*W+r⌋₊+1
  let test (m : ℕ) := ∀ z∈Icc (-r) r, (((shift+m:ℕ):ℝ)+z)/W∈S
  let mass := r^(2^N-2)*∏ i : K, f i
  have hr := (physicalArc_spec hε.1 hε.2).1
  have htick := (hclock ε hε).2
  rw [product] at htick
  have hrate := filtered_tick_rate test (((shift:ℝ)-r)/W) (1/W) mass (one_div_pos.mpr hW) htick
  have hcell (n : ℤ) (z : ℝ) (hz : z∈Ico (-(1/2):ℝ) (1/2)) (hu : ((n:ℝ)+z)/W∈S) : z∈Icc (-r) r := by
    have hx := (visit_iff_offsets w p q he hspan hr.1.le hr.2 n hz).mp
      ((physical_visit H hε.1 hε.2 _).mpr hu)
    exact offsets_bound (show θ p=1 from div_self hW.ne') (show θ q=0 by simp only [θ,sub_self,zero_div]) _ _ hx
  have hrec (u T) : u∈F T ↔ σ<u ∧ u≤T ∧ Entry S u := by
    change u∈entryDates E r T \ entryDates E r σ ↔ _
    have hx := (hflux k ε hε.1 hε.2).1
    rw [Finset.mem_sdiff,hx,hx]
    constructor
    · rintro ⟨⟨hu,ht,hv⟩,hh⟩
      exact ⟨lt_of_not_ge (fun hs => hh ⟨hu,hs,hv⟩),ht,hv⟩
    · rintro ⟨ha,ht,hv⟩
      exact ⟨⟨hσ.trans ha,ht,hv⟩,fun h => ha.not_ge h.2.1⟩
  have hshift : σ*W+r < shift ∧ (shift:ℝ) ≤ σ*W+r+1 := by
    simp only [shift,Nat.cast_add,Nat.cast_one]
    exact ⟨Nat.lt_floor_add_one _,add_le_add_right (Nat.floor_le (add_nonneg (mul_nonneg hσ.le hW.le) hr.1.le)) _⟩
  have hnum : Tendsto (fun T : ℝ => ((longVisits S (2*r/W) (F T)).card:ℝ)/T) atTop (𝓝 (mass/(1/W))) :=
    hrate.congr fun T => by rw [full_residence_count hW hr.1.le hr.2 hcell F hrec shift hshift T]
  have hden := entries_after_rate E (maximallyProjectiveEnergy_neg (hi k)) hr.1 hr.2 σ
  have hcI : Fintype.card (Fin N→Bool)=2^N := by simp
  rw [hcI] at hden
  have hfac : Tendsto (fun T : ℝ => (T-σ)/T) atTop (𝓝 1) := by
    have h := ((tendsto_id (x := (atTop : Filter ℝ))).const_div_atTop σ).const_sub 1
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    change 1-σ/T=(T-σ)/T
    field_simp [hT.ne']
  have htot := hden.mul hfac
  rw [mul_one] at htot
  have hquot := hnum.div htot (mul_pos (pow_pos hr.1 _) hR).ne'
  have heq : (mass/(1/W))/(r^(2^N-2)*pairTurnRate E)=A := by
    dsimp only [mass,A]
    field_simp [(pow_pos hr.1 (2^N-2)).ne',hR.ne',hW.ne']
    <;> ring
  rw [heq] at hquot
  refine hquot.congr' ?_
  filter_upwards [eventually_gt_atTop σ] with T hT
  change _/T/(((F T).card:ℝ)/(T-σ)*((T-σ)/T))=_
  rw [show ((F T).card:ℝ)/(T-σ)*((T-σ)/T)=((F T).card:ℝ)/T by
    field_simp [(sub_pos.mpr hT).ne',(hσ.trans hT).ne']]
  exact div_div_div_cancel_right₀ (hσ.trans hT).ne' _ _

#print axioms gaussian_maximum_entry_atom
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
