import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.FirstPrice
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GrowingHorizon.LogarithmicWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # A bond sweep bridges the whole short-lag cluster before the first robust exit -/

open Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpanningRecords
open RepeatedGates.PhysicalBlocks PrecisionReturns
noncomputable section

abbrev prefix (ω : PathPauliDisorder) (n : ℕ) : selfAdjoint (Register (n+2)) :=
  ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩

private theorem sweep_margin {A B m t M : ℝ} (hA : 0<A) (hB : 0<B) (hm : 0<m)
    (hs : 13440*B*A^2<m) (ht : 0≤t) (ht' : t≤A/m) (hM : M≤B*(m+1)) (hm' : 1≤m) :
    t^2*(84*M)<1/80 := by
  have hM' : M≤2*B*m := hM.trans (by nlinarith only [mul_nonneg hB.le (sub_nonneg.mpr hm')])
  calc
    _ ≤ t^2*(84*(2*B*m)) := mul_le_mul_of_nonneg_left (by linarith only [hM']) (sq_nonneg _)
    _ ≤ (A/m)^2*(84*(2*B*m)) := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht ht' 2) (by positivity)
    _ = 168*B*A^2/m := by field_simp; ring
    _ < 1/80 := (div_lt_iff₀ hm).mpr (by linarith only [hs])

/-- From every visit, the first spanning-budget crossing is later
than any prescribed inverse-size lag and occurs by time one. The
initial circuit and the additional budget may depend on the visit. -/
theorem gaussian_crossing_delay (A : ℝ) (hA : 0<A) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ (v : ℝ) (s q : ℕ) (η : ℝ),
      η∈Icc (9/80:ℝ) (1/8) →
      HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution (prefix ω n).val v) →
      ((2*s+q:ℕ):ℝ)≤prescribedExcess 1*(n+1:ℕ) →
      let u := firstExcessAfter ω n (s+q) v η
      A/(n+1:ℕ)<u ∧ u≤1 ∧ orbitCircuitDistance (prefix ω n) (n+1+(s+q)) (v+u)=η ∧
        ∀ h∈Ico 0 u, orbitCircuitDistance (prefix ω n) (n+1+(s+q)) (v+h)<η := by
  obtain ⟨_,B,_,hB,hmass⟩ := gaussian_path_eventual_coefficient_mass
  obtain ⟨n₀,hn₀⟩ := exists_nat_gt (13440*B*A^2)
  filter_upwards [hmass,gaussian_prescribed_excess (by norm_num : (0:ℝ)<1)] with ω hm hh
  filter_upwards [hm,hh,eventually_ge_atTop n₀] with n hm hn hn'
  intro v s q η hη hv hq
  have hinc : ¬HasProjectiveCircuitApproximation (n+2) (1/10+η) (s+(n+1+(s+q)))
      (unitaryEvolution (prefix ω n).val 1) := by
    rintro ⟨z,hz,C,hC,he⟩
    have h := hn _ ⟨z,hz,C,hC,he.trans (by linarith only [hη.2])⟩
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] at h hq
    linarith only [h,hq]
  let u := firstExcessAfter ω n (s+q) v η
  obtain ⟨hu,hu₁,he,hpre⟩ := firstExcessAfter_le_of_increment ω n s q (by norm_num : (0:ℝ)≤1)
    (by linarith only [hη.1] : (1/10:ℝ)<η) hv hinc
  refine ⟨?_,hu₁,he,hpre⟩
  by_contra! hus
  let x := pathPauliDisorderShell ω n
  have hs : 13440*B*A^2<(n+1:ℕ) := hn₀.trans_le (by exact_mod_cast Nat.le_succ_of_le hn')
  have hh := sweep_margin hA hB (by positivity : (0:ℝ)<(n+1:ℕ)) hs hu hus
    (show ‖x‖^2 ≤ B*((n+1:ℕ)+1:ℝ) by simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
      add_assoc,one_add_one_eq_two] using hm.2) (by exact_mod_cast Nat.succ_pos n)
  obtain ⟨z,hz,C,hC,hfit⟩ := BondProducts.bond_sweep_error x u hu 1 one_pos
  let g := u^2*(84*‖x‖^2)
  have ht : HasProjectiveCircuitApproximation (n+2) g (n+1) (unitaryEvolution (prefix ω n).val u) :=
    ⟨z,hz,C,by simpa only [one_mul] using hC.le,by simpa only [Nat.cast_one,div_one] using hfit⟩
  obtain ⟨w,hw,D,hD,hd⟩ := affordable_add_time (prefix ω n) (x:=v) (y:=u) hv ht
  have hle : orbitCircuitDistance (prefix ω n) (n+1+(s+q)) (v+u)≤1/10+g :=
    (hasProjectiveCircuitApproximation_iff_infDist ..).mp ⟨w,hw,D,hD.trans (by omega),hd⟩
  rw [he] at hle
  change g<1/80 at hh
  linarith only [hle,hh,hη.1]

#print axioms gaussian_crossing_delay
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpanningRecords

