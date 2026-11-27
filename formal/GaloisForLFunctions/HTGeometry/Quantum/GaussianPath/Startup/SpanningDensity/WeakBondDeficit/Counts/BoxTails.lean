import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.BondMinimum
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.DisjointWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.GaussianBonds

/-! # Two-sided frequency bounds for nine-dimensional weak bonds -/

open MeasureTheory ProbabilityTheory Set Finset Real Polynomial
open scoped Classical
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open BlockDilations.AdaptiveCuts
noncomputable section

/-- Nine Pauli coefficients at the physical bond numbered i. -/
def bondRow9 (ω : PathPauliDisorder) (i : ℕ) (k : Fin 9) : ℝ :=
  ω (i,Sum.inr ((finProdFinEquiv (m:=3) (n:=3)).symm k))

private def rowCount (ω : PathPauliDisorder) (s d m : ℕ) (B : Set (Fin 9→ℝ)) : ℕ :=
  (univ.filter (fun i : Fin m => bondRow9 ω (s+d*i.val)∈B)).card

def boxCount (ω : PathPauliDisorder) (s d m : ℕ) (h : ℝ) : ℕ :=
  rowCount ω s d m (weakBond h)

private theorem complementary_counts (ω : PathPauliDisorder) (s d m : ℕ) (B : Set (Fin 9→ℝ)) :
    rowCount ω s d m B + rowCount ω s d m Bᶜ = m := by
  let P (i : Fin m) := bondRow9 ω (s+d*i.val)∈B
  have h₁ : rowCount ω s d m B=(univ.filter P).card := by
    apply congrArg Finset.card
    ext i
    simp only [mem_filter,P]
  have h₂ : rowCount ω s d m Bᶜ=(univ.filter fun i => ¬P i).card := by
    apply congrArg Finset.card
    ext i
    simp only [mem_filter,P,Set.mem_compl_iff]
  rw [h₁,h₂,card_filter_add_card_filter_not,card_univ,Fintype.card_fin]

private theorem row_law (s d m : ℕ) (hd : 0<d) :
    MeasurePreserving (fun ω (i : Fin m) => bondRow9 ω (s+d*i.val))
      pathPauliDisorderLaw (Measure.infinitePi fun _ : Fin m => bondLaw) := by
  let f (j : Fin m×Fin 9) : ℕ×PathPauliDirections :=
    (s+d*j.1.val,Sum.inr ((finProdFinEquiv (m:=3) (n:=3)).symm j.2))
  have hf : Function.Injective f := by
    rintro ⟨i,k⟩ ⟨j,l⟩ h
    obtain ⟨h₁,h₂⟩ := Prod.mk.inj h
    apply Prod.ext
    · exact Fin.ext (Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel h₁))
    · exact (finProdFinEquiv (m:=3) (n:=3)).symm.injective (Sum.inr.inj h₂)
  have h := FixedHorizon.disjoint_window_law (gaussianReal 0 1) f hf
  change MeasurePreserving (fun (ω : PathPauliDisorder) (j : Fin m) (k : Fin 9) => ω (f (j,k)))
    (Measure.infinitePi fun _ => gaussianReal 0 1)
    (Measure.infinitePi fun _ : Fin m => Measure.pi fun _ : Fin 9 => gaussianReal 0 1)
  simpa only [Measure.infinitePi_eq_pi] using h

/-- The one-bond box probability is comparable to h⁹ up to h=1. -/
theorem box_probability {h : ℝ} (hh : 0<h) (h₁ : h≤1) :
    (2*gaussianDensityFloor)^9*h^9≤bondLaw.real (weakBond h) ∧
      bondLaw.real (weakBond h)≤4^9*h^9 := by
  let γ := gaussianReal 0 1
  have hlo := ENNReal.toReal_mono (measure_ne_top γ _) (gaussianReal_Icc_lower h₁)
  rw [ENNReal.toReal_ofReal (mul_nonneg gaussianDensityFloor_pos.le (mul_nonneg zero_le_two hh.le))] at hlo
  have hhi : γ.real (Icc (-h) h)≤4*h := by
    have hs : Icc (-h) h⊆{x : ℝ | |x|<2*h} := fun x hx => (abs_le.mpr hx).trans_lt (by linarith only [hh])
    apply (measureReal_mono (μ:=γ) hs (measure_ne_top _ _)).trans
    have hp := gaussian_polynomial_sublevel (Polynomial.X:ℂ[X]) (2*h) (by positivity)
    simpa only [Polynomial.eval_X,Polynomial.leadingCoeff_X,norm_one,Polynomial.natDegree_X,
      pow_one,one_mul,Nat.cast_one,mul_one,Complex.norm_real,Real.norm_eq_abs,show 2*(2*h)=4*h by ring] using hp
  rw [weakBond_mass,←mul_pow,←mul_pow]
  have hlow : 2*gaussianDensityFloor*h≤γ.real (Icc (-h) h) := calc
    _ = gaussianDensityFloor*(2*h) := by ring
    _ ≤ _ := hlo
  refine ⟨pow_le_pow_left₀ (mul_nonneg (mul_nonneg zero_le_two gaussianDensityFloor_pos.le) hh.le) hlow 9,
    pow_le_pow_left₀ measureReal_nonneg hhi 9⟩

private theorem finite_count_tail {m : ℕ} [NeZero m] (s d : ℕ) (hd : 0<d)
    (B : Set (Fin 9→ℝ)) (hB : MeasurableSet B) {η : ℝ} (hη : 0≤η) :
    pathPauliDisorderLaw.real {ω | (bondLaw.real B+η)*m≤(rowCount ω s d m B:ℝ)}≤exp (-2*η^2*m) := by
  let A := {x : Fin m→(Fin 9→ℝ) | (bondLaw.real B+η)*m≤((univ.filter fun j => x j∈B).card:ℝ)}
  have hA : MeasurableSet A := by
    have hcn (x : Fin m→(Fin 9→ℝ)) :
        (∑ j, B.indicator (fun _ => (1:ℝ)) (x j))=((univ.filter fun j => x j∈B).card:ℝ) := by
      simp only [Set.indicator_apply,Finset.sum_boole]
    change MeasurableSet {x | (bondLaw.real B+η)*m≤_}
    simp_rw [←hcn]
    exact measurableSet_le measurable_const (Finset.measurable_sum _ fun j _ =>
      (measurable_const.indicator hB).comp (measurable_pi_apply j))
  have h := (row_law s d m hd).measureReal_preimage hA.nullMeasurableSet
  apply h.le.trans
  simpa only [A,Fintype.card_fin] using FixedHorizon.independent_window_failures bondLaw
    (fun _ : Fin m => B) (fun _ => hB) (fun _ => le_rfl) hη

/-- The event is measured on the original chain. Different bond
subsequences may overlap, since each tail uses one progression. -/
theorem physical_box_count_tails {m : ℕ} [NeZero m] (s d : ℕ) (hd : 0<d) (h : ℝ) :
    let p := bondLaw.real (weakBond h)
    pathPauliDisorderLaw.real {ω | (boxCount ω s d m h:ℝ)≤p*m/2 ∨
      (3:ℝ)/2*p*m≤boxCount ω s d m h}≤2*exp (-2*(p/2)^2*m) := by
  intro p
  let B := weakBond h
  let ν := pathPauliDisorderLaw
  letI : IsProbabilityMeasure ν := by dsimp only [ν,pathPauliDisorderLaw]; infer_instance
  let upper := {ω | (p+p/2)*m≤(boxCount ω s d m h:ℝ)}
  let lower := {ω : PathPauliDisorder | (bondLaw.real Bᶜ+p/2)*m≤(rowCount ω s d m Bᶜ:ℝ)}
  have hp : 0≤p/2 := div_nonneg measureReal_nonneg zero_le_two
  have hu : ν.real upper≤_ := finite_count_tail (m:=m) s d hd B (weakBond_measurable _) hp
  have hl : ν.real lower≤_ := finite_count_tail (m:=m) s d hd Bᶜ (weakBond_measurable _).compl hp
  apply ((measureReal_mono (μ:=ν) (s₂:=lower∪upper) ?_ (measure_ne_top _ _)).trans (measureReal_union_le ..)).trans
    ((add_le_add hl hu).trans_eq (two_mul _).symm)
  intro ω hω
  rcases hω with hx|hx
  · left
    have hs := complementary_counts ω s d m B
    have hs' := congrArg (fun k : ℕ => (k:ℝ)) hs
    rw [Nat.cast_add] at hs'
    change (bondLaw.real Bᶜ+p/2)*m≤_
    rw [measureReal_compl (weakBond_measurable h),probReal_univ]
    change (boxCount ω s d m h:ℝ)≤p*m/2 at hx
    change (boxCount ω s d m h:ℝ)+_=m at hs'
    change (1-p+p/2)*m≤(rowCount ω s d m Bᶜ:ℝ)
    linarith only [hx,hs']
  · right
    change (p+p/2)*m≤_
    linarith only [hx]

#print axioms physical_box_count_tails
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
