import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.ExtremeClock.ClockCell
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.CrossingWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # First physical empty return on the integer clock of the extreme energies -/
open Filter MeasureTheory Finset Real Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
open SharpOccupation
noncomputable section

/-- A cell qualifies when any of its admissible offsets lies beyond the
physical observation origin, expressed in units of the extreme gap. -/
def qualifying {I : Type*} (θ : I→ℝ) (r cut : ℝ) : Set ℤ :=
  {n | ∃ z∈offsets θ n r, cut≤(n:ℝ)+z}

private theorem first_cell {N : ℕ} (H : selfAdjoint (Register N)) (p q : Fin N→Bool) (a : ℝ)
    {ε : ℝ} (hε : ε∈Ioo (0:ℝ) (sqrt 2)) :
    let w := fun i => -H.2.isHermitian.eigenvalues i/(2*π)
    let W := w p-w q
    let θ := fun i => (w i-w q)/W
    let v := PrecisionReturns.firstVisit H a 0 ε
    let r := physicalArc ε
    w q<w p → (∀ i, w q≤w i ∧ w i≤w p) →
    ∃ n : ℤ, IsLeast (qualifying θ r (a*W)) n ∧
      ∃ z, IsLeast {z∈offsets θ n r | a*W≤(n:ℝ)+z} z ∧ v=((n:ℝ)+z)/W := by
  intro w W θ v r he hb
  have hW : 0<W := sub_pos.mpr he
  have hθp : θ p=1 := div_self hW.ne'
  have hθq : θ q=0 := by simp only [θ,sub_self,zero_div]
  have hr := (physicalArc_spec hε.1 hε.2).1
  have hleast := PrecisionReturns.firstVisit_isLeast H a 0 hε.1
  have hav : a≤v := hleast.1.1
  have hv : flow w v∈enclosingUnitArc r := (physical_visit H hε.1 hε.2 v).mpr hleast.1.2
  let n := ⌊v*W+1/2⌋
  let z := v*W-(n:ℝ)
  have hn₀ : (n:ℝ)≤v*W+1/2 := Int.floor_le _
  have hn₁ : v*W+1/2<(n:ℝ)+1 := Int.lt_floor_add_one _
  have hz : z∈Ico (-(1/2):ℝ) (1/2) := ⟨by dsimp only [z]; linarith only [hn₀],
    by dsimp only [z]; linarith only [hn₁]⟩
  have hdate : v=((n:ℝ)+z)/W := (eq_div_iff hW.ne').mpr (by dsimp only [z]; ring)
  have hfit := (visit_iff_offsets w p q he hb hr.1.le hr.2 n hz).mp (hdate ▸ hv)
  have hcut : a*W≤(n:ℝ)+z := (mul_le_mul_of_nonneg_right hav hW.le).trans_eq ((eq_div_iff hW.ne').mp hdate)
  have compare (m : ℤ) (u : ℝ) (hu : u∈offsets θ m r) (ha : a*W≤(m:ℝ)+u) :
      (n:ℝ)+z≤(m:ℝ)+u := by
    have hbound := offsets_bound hθp hθq m r hu
    have hu' : u∈Ico (-(1/2):ℝ) (1/2) :=
      ⟨(neg_le_neg hr.2.le).trans hbound.1,hbound.2.trans_lt hr.2⟩
    have hflow := (visit_iff_offsets w p q he hb hr.1.le hr.2 m hu').mpr hu
    have hvis := (physical_visit H hε.1 hε.2 _).mp hflow
    have htime := hleast.2 ⟨(le_div_iff₀ hW).mpr ha,hvis⟩
    change v≤((m:ℝ)+u)/W at htime
    exact ((eq_div_iff hW.ne').mp hdate).symm.trans_le ((le_div_iff₀ hW).mp htime)
  refine ⟨n,⟨⟨z,hfit,hcut⟩,?_⟩,z,⟨⟨hfit,hcut⟩,?_⟩,hdate⟩
  · rintro m ⟨u,hu,ha⟩
    by_contra! h
    have hmn : (m:ℝ)+1≤(n:ℝ) := by exact_mod_cast (show m+1≤n by omega)
    have hz' := offsets_bound hθp hθq n r hfit
    have hu' := offsets_bound hθp hθq m r hu
    linarith only [compare m u hu ha,hmn,hz'.1,hu'.2,hr.2]
  · rintro u ⟨hu,ha⟩
    exact le_of_add_le_add_left (compare n u hu ha)

/-- At every fixed physical tolerance, the first return after the true
near-Hilbert crossing is the first qualifying integer cell and its least
admissible offset. Membership uses only real linear inequalities in the
centered multiples of the normalized gaps of this same frozen prefix. -/
theorem gaussian_first_return_cell :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let w := fun i => -H.2.isHermitian.eigenvalues i/(2*π)
      ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        ∃ p q, w q<w p ∧ (∀ i, w q≤w i ∧ w i≤w p) ∧
          ∀ ε∈Ioo (0:ℝ) (sqrt 2), let r := physicalArc ε
            let W := w p-w q
            let θ := fun i => (w i-w q)/W
            ∃ n : ℤ, IsLeast (qualifying θ r (σ*W)) n ∧
              ∃ z, IsLeast {z∈offsets θ n r | σ*W≤(n:ℝ)+z} z ∧
                PrecisionReturns.firstVisit H σ 0 ε=((n:ℝ)+z)/W := by
  filter_upwards [gaussian_first_crossing_flux,gaussian_path_all_prefixes_maximally_projective] with ω hc hi
  filter_upwards [hc] with k hk
  intro N H P w
  obtain ⟨σ,hσ,he,hb,_⟩ := hk
  obtain ⟨p,_,hp⟩ := exists_mem_eq_sup' univ_nonempty w
  obtain ⟨q,_,hq⟩ := exists_mem_eq_inf' univ_nonempty w
  have bounds (i) : w q≤w i ∧ w i≤w p := by
    rw [←hp,←hq]
    exact ⟨inf'_le w (mem_univ i),le_sup' w (mem_univ i)⟩
  have hgap : w q<w p := by
    by_contra! h
    have hall (i) : w i=w q := le_antisymm ((bounds i).2.trans h) (bounds i).1
    obtain ⟨i,j,hij⟩ := exists_pair_ne (Fin N→Bool)
    have he := (hall i).trans (hall j).symm
    exact hij ((hi k).injective (neg_inj.mp ((div_left_inj' (by positivity : (2:ℝ)*π≠0)).mp he)))
  exact ⟨σ,hσ,he,hb,p,q,hgap,bounds,fun ε hε => first_cell H p q σ hε hgap bounds⟩

#print axioms gaussian_first_return_cell
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
