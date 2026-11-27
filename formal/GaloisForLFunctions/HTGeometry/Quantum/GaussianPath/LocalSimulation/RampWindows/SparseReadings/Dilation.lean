import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.ScaledWindows
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation

/-! # Finite-date circuit exclusion by separating Gaussian dilations -/

open Set MeasureTheory Filter Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches.RampWindows.SparseReadings
open PrescribedTimes PrescribedTimes.ShortWindows
noncomputable section

/-- The observation origin is either the identity date or the first robust crossing. -/
def origin (n : ℕ) (P : Option ℕ) (x : PrefixIndex n → ℝ) : ℝ :=
  P.elim 0 (fun j => crossingOrigin n j (9/80) x)

private theorem origin_measurable (n : ℕ) (P : Option ℕ) : Measurable (origin n P) := by
  cases P with
  | none => exact measurable_const
  | some j => exact measurable_crossingOrigin n j _

private theorem scale_origin {n : ℕ} (P : Option ℕ) {a : ℝ} (ha : 0 < a)
    (x : PrefixIndex n → ℝ) : a*origin n P (a • x) = origin n P x := by
  cases P with
  | none => exact mul_zero _
  | some j => exact smul_crossingOrigin n j _ ha x

/-- A fit by any circuit within the budget, anywhere in the observation window. -/
def visit (n s : ℕ) (P : Option ℕ) (T w : ℝ) : Set (PrefixIndex n → ℝ) :=
  {x | ∃ t ∈ Icc (origin n P x+T) (origin n P x+T+w), pathGateDistance n s x t ≤ 1/8}

theorem measurable_visit (n s : ℕ) (P : Option ℕ) (T w : ℝ) :
    MeasurableSet (visit n s P T w) :=
  measurable_shifted_sublevel _ (continuous_distance n s) _ (origin_measurable n P) T w _

/-- A positive cheap lag for the concatenation of two fitted circuits. -/
def cheapLag (n s : ℕ) (l H : ℝ) : Set (PrefixIndex n → ℝ) :=
  {x | ∃ t ∈ Icc l H, pathGateDistance n (s+s) x t ≤ 1/4}

theorem measurable_cheapLag (n s : ℕ) (l H : ℝ) : MeasurableSet (cheapLag n s l H) := by
  simpa only [cheapLag,zero_add,show l+(H-l)=H by ring] using
    measurable_shifted_sublevel _ (continuous_distance n (s+s))
      (fun _ => (0:ℝ)) measurable_const l (H-l) (1/4)

private theorem lag_of_visits {k s : ℕ} (ω : PathPauliDisorder) (t v : ℝ)
    (ht : pathGateDistance (k+1) s (prefixPoint k ω) t ≤ 1/8)
    (hv : pathGateDistance (k+1) s (prefixPoint k ω) v ≤ 1/8) :
    pathGateDistance (k+1) (s+s) (prefixPoint k ω) |v-t| ≤ 1/4 := by
  let u := pathPauliDisorderShell ω (k+1)
  let H : selfAdjoint (Matrix (Fin (k+3) → Bool) (Fin (k+3) → Bool) ℂ) :=
    ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  have eqH : numberedGenerator (k+1) (prefixPoint k ω) = H.val := numberedGenerator_shell u
  have ordered (a b : ℝ) (ha : pathGateDistance (k+1) s (prefixPoint k ω) a ≤ 1/8)
      (hb : pathGateDistance (k+1) s (prefixPoint k ω) b ≤ 1/8) :
      pathGateDistance (k+1) (s+s) (prefixPoint k ω) (b-a) ≤ 1/4 := by
    simp only [pathGateDistance,eqH] at ha hb ⊢
    have h := affordable_add_time H
      (((hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr ha).neg_time H)
      ((hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr hb)
    rw [show -a+b=b-a by ring,show (1/8:ℝ)+1/8=1/4 by norm_num] at h
    exact (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp h
  rcases le_total t v with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact ordered t v ht hv
  · rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr h)]
    exact ordered v t hv ht

private theorem isolated_visit {k s m : ℕ} (P : Option ℕ) (ω : PathPauliDisorder)
    {g T w l H : ℝ} (hg : 0 ≤ g) (hT : 0 < T) (hspan : (m:ℝ)*g ≤ T)
    (hw : 0≤w) (hl : l ≤ g/2-2*w) (hh : (m:ℝ)*g+2*w ≤ H)
    (hfit : prefixPoint k ω ∈ visit (k+1) s P T w)
    (hgood : prefixPoint k ω ∉ cheapLag (k+1) s l H) :
    prefixPoint k ω ∈ isolated (factor (m:=m) g T) (visit (k+1) s P T w) := by
  let x := prefixPoint k ω
  apply mem_isolated hfit
  obtain ⟨t,ht,hd⟩ := hfit
  intro i j hji
  let p := factor g T j / factor g T i
  have hp : 0 < p := div_pos (zero_lt_one.trans_le (factor_bounds hg hT hspan j).1)
    (zero_lt_one.trans_le (factor_bounds hg hT hspan i).1)
  rintro ⟨v,hv,hc⟩
  have ho := scale_origin P hp x
  have hleft := mul_le_mul_of_nonneg_left hv.1 hp.le
  have hright := mul_le_mul_of_nonneg_left hv.2 hp.le
  change p*(origin (k+1) P (p • x)+T) ≤ p*v at hleft
  change p*v ≤ p*(origin (k+1) P (p • x)+T+w) at hright
  simp only [mul_add,ho] at hleft hright
  obtain ⟨hlo,hhi⟩ := window_gap hg hT hspan hw i j hji ht ⟨hleft,hright⟩
  rw [distance_dilate] at hc
  exact hgood ⟨|p*v-t|,⟨hl.trans hlo,hhi.trans hh⟩,lag_of_visits ω t (p*v) hd hc⟩

/-- On draws without a cheap lag, every window hit occupies a distinct
row in the dilation grid. The dimension only limits the span of the grid. -/
theorem window_grid_mass {k s m : ℕ} (P : Option ℕ) {g T w l H : ℝ}
    (hm : 0 < m) (hg : 0≤g) (hT : 0 < T) (hspan : (m:ℝ)*g ≤ T)
    (hprice : (Fintype.card (PrefixIndex (k+1)):ℝ)*((m:ℝ)*g) ≤ T)
    (hw : 0≤w) (hl : l ≤ g/2-2*w) (hh : (m:ℝ)*g+2*w ≤ H) :
    pathPauliDisorderLaw.real (prefixPoint k ⁻¹'
      (visit (k+1) s P T w \ cheapLag (k+1) s l H)) ≤ exp 1/m := by
  let E := visit (k+1) s P T w
  let a := factor (m:=m) g T
  have ha (i : Fin m) : 1 ≤ a i := (factor_bounds hg hT hspan i).1
  have hp (i : Fin m) : (Fintype.card (PrefixIndex (k+1)):ℝ)*(a i-1) ≤ 1 := by
    change _*(1+(i.val:ℝ)*g/T-1) ≤ 1
    rw [add_sub_cancel_left,←mul_div_assoc,div_le_one hT]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (by exact_mod_cast i.isLt.le : (i.val:ℝ) ≤ m) hg) (Nat.cast_nonneg _)).trans hprice
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  have hsub : prefixPoint k ⁻¹' (E \ cheapLag (k+1) s l H) ⊆ prefixPoint k ⁻¹' isolated a E :=
    fun ω h => isolated_visit P ω hg hT hspan hw hl hh h.1 h.2
  apply (measureReal_mono hsub).trans
  rw [(gaussian_pauli_prefix_coordinates_law (k+1)).measureReal_preimage
    (measurable_isolated a (measurable_visit ..)).nullMeasurableSet]
  apply (le_div_iff₀ (Nat.cast_pos.mpr hm : (0:ℝ) < m)).mpr
  rw [mul_comm]
  exact gaussian_isolated_mass (measurable_visit ..) ha hp

#print axioms window_grid_mass
end
end GaloisForLFunctions.HTGeometry.LocalPatches.RampWindows.SparseReadings
