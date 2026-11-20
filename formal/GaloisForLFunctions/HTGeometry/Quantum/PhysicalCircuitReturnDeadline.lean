import GaloisForLFunctions.HTGeometry.ProjectiveOperatorNormReturnTarget
import GaloisForLFunctions.HTGeometry.FidelityPhaseRadius
import GaloisForLFunctions.HTGeometry.UniformProjectiveContinuousCircuitFirstReturnLaw
import GaloisForLFunctions.HTGeometry.ProjectiveContinuousCircuitConeLaw
import GaloisForLFunctions.HTGeometry.Quantum.TranslatedCircuitOccupation

/-!
# A delayed first entrance to the physical circuit set

A simultaneous Dirichlet return of the anchored eigenphases gives a literal
operator-norm approximation by the empty circuit. Compactness supplies the
first entrance to the full circuit budget after any prescribed time.
-/

open Set Topology MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem chord_le_of_turns_close (x : ℝ) (Q : ℕ)
    (h : latticeClose (x/(2*Real.pi)) (1/(Q+1 : ℝ))) :
    ‖Complex.exp (-(Complex.I*(x : ℂ))) - 1‖ ≤ 2*Real.pi/(Q+1:ℝ) := by
  obtain ⟨m,hm⟩ := h
  rw [norm_exp_neg_I_mul_sub_one, mul_comm Complex.I]
  have hc := norm_expI_sub_expI_le x 0 m
  simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,sub_zero] at hc
  have hpi : 0 < 2*Real.pi := by positivity
  apply hc.trans
  rw [show x-2*Real.pi*m = 2*Real.pi*(x/(2*Real.pi)-m) by field_simp,
    abs_mul,abs_of_pos hpi]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hm.le hpi.le

/-- After any specified time A, one multiple of |A|+1 returns the whole
operator up to phase, with the Dirichlet exponent equal to the number of
relative phases. No spectral genericity is required. -/
theorem projective_operator_zero_gate_return_after {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d+1)) (H : selfAdjoint (Reg n)) (A : ℝ) (Q : ℕ) :
    ∃ t ∈ Icc (|A|+1) ((|A|+1)*((Q+1:ℝ)^d)),
      HasProjectiveCircuitApproximation n (2*Real.pi/(Q+1:ℝ)) 0 (unitaryEvolution (H : Reg n) t) := by
  let E := H.2.isHermitian.eigenvalues
  let a := e.symm 0
  let tick := |A|+1
  let β (j : Fin d) := tick*(E (e.symm j.succ)-E a)/(2*Real.pi)
  obtain ⟨q,hq,hQ,hb⟩ := exists_simultaneous_dirichlet β (Nat.succ_pos Q)
  let t := tick*q
  have htick : 0 < tick := by dsimp [tick]; positivity
  have h1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  have h2 : (q:ℝ) ≤ (Q+1:ℝ)^d := by exact_mod_cast hQ
  refine ⟨t,⟨?_,mul_le_mul_of_nonneg_left h2 htick.le⟩,?_⟩
  · change tick ≤ tick*q
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h1 htick.le
  refine ⟨anchorPhase E a t,by simp [anchorPhase,Complex.norm_exp],TwoQubitCircuit.one n,by rfl,?_⟩
  rw [TwoQubitCircuit.one_eval]
  change ‖unitaryEvolution (H : Reg n) t - anchorPhase E a t • (1:Reg n)‖ ≤ _
  rw [l2_opNorm_unitaryEvolution_sub_anchorPhase H.2.isHermitian a t]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*Real.pi/(Q+1:ℝ))).mpr
  intro i
  let x := t * (E i-E a)
  have he : -(Complex.I * ((t:ℂ) * ((E i:ℂ)-(E a:ℂ)))) = -(Complex.I*(x:ℂ)) := by
    dsimp [x]; push_cast; rfl
  change ‖Complex.exp (-(Complex.I*((t:ℂ)*((E i:ℂ)-(E a:ℂ))))) - 1‖ ≤ _
  rw [he]
  apply chord_le_of_turns_close x Q
  dsimp only [x]
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  refine Fin.cases ?_ (fun k => ?_) j
  · refine ⟨0,?_⟩
    simp only [a,sub_self,mul_zero,zero_div,Int.cast_zero,abs_zero]
    positivity
  · have h := hb k
    have hz : t*(E (e.symm k.succ)-E a)/(2*Real.pi) = (q:ℝ)*β k := by dsimp [t,β]; ring
    change latticeClose (t*(E (e.symm k.succ)-E a)/(2*Real.pi)) _
    rw [hz]
    simpa only [Nat.cast_succ] using h

private theorem closed_physical_circuit_hits {n : ℕ} (H : selfAdjoint (Reg n)) (s : ℕ) (ε : ℝ) :
    IsClosed {t | HasProjectiveCircuitApproximation n ε s (unitaryEvolution (H : Reg n) t)} := by
  let K := phaseCircuitMatrixImageAtMost n s
  have hK := isCompact_phaseCircuitMatrixImageAtMost n s
  have hne := phaseCircuitMatrixImageAtMost_nonempty n s
  have hL : LipschitzWith ⟨‖(H : Reg n)‖,norm_nonneg _⟩ (unitaryEvolution (H : Reg n)) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    change dist (unitaryEvolution (H : Reg n) u) (unitaryEvolution H v) ≤ ‖(H : Reg n)‖ * dist u v
    rw [dist_eq_norm, Real.dist_eq]
    exact norm_unitaryEvolution_time_sub_le H.2 u v
  have heq (t : ℝ) : HasProjectiveCircuitApproximation n ε s (unitaryEvolution (H : Reg n) t) ↔
      Metric.infDist (unitaryEvolution (H : Reg n) t) K ≤ ε := by
    constructor
    · rintro ⟨c,hc,C,hC,h⟩
      have hmem : c • (C.eval : Reg n) ∈ K := mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨c,hc,C,hC,rfl⟩
      exact (Metric.infDist_le_dist_of_mem hmem).trans (by simpa only [dist_eq_norm] using h)
    · intro h
      obtain ⟨U,hU,hd⟩ := exists_compactTarget_minDist hK hne (unitaryEvolution (H : Reg n) t)
      obtain ⟨c,hc,C,hC,rfl⟩ := mem_phaseCircuitMatrixImageAtMost_iff.mp hU
      exact ⟨c,hc,C,hC,by rwa [← hd,dist_eq_norm] at h⟩
  simp only [heq]
  exact isClosed_compactTargetCaptureTimeSet _ hL.continuous K ε

/-- The first visit at or after A to the complete s-gate set at error 1/10
is attained and has an explicit upper deadline, including for A determined
by the Hamiltonian. -/
theorem projective_first_circuit_visit_deadline {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d+1)) (H : selfAdjoint (Reg n)) (A : ℝ) (s : ℕ) :
    ∃ v ∈ Icc A ((|A|+1)*(100:ℝ)^d),
      HasProjectiveCircuitApproximation n (1/10:ℝ) s (unitaryEvolution (H : Reg n) v) ∧
      ∀ t ∈ Ico A v, ProjectiveCircuitSeparated n (1/10:ℝ) s (unitaryEvolution (H : Reg n) t) := by
  let E := {t | HasProjectiveCircuitApproximation n (1/10:ℝ) s (unitaryEvolution (H : Reg n) t)}
  let B := (|A|+1)*(100:ℝ)^d
  have hcomp : IsCompact (Icc A B ∩ E) :=
    isCompact_Icc.inter_right (closed_physical_circuit_hits H s _)
  obtain ⟨u,hu,c,hc,C,hC,h⟩ := projective_operator_zero_gate_return_after e H A 99
  have huB : u ≤ B := by
    have hu' := hu.2
    rw [show ((99:ℕ):ℝ)+1 = 100 by norm_num] at hu'
    exact hu'
  have heasy : u ∈ E := by
    refine ⟨c,hc,C,by omega,h.trans ?_⟩
    have hp := Real.pi_lt_four
    linarith
  have hne : (Icc A B ∩ E).Nonempty :=
    ⟨u,⟨by linarith only [le_abs_self A,hu.1],huB⟩,heasy⟩
  obtain ⟨v,hv,hmin⟩ := hcomp.exists_isMinOn hne continuous_id.continuousOn
  refine ⟨v,hv.1,hv.2,?_⟩
  intro t ht c hc C hC
  by_contra! h
  have htE : t ∈ E := ⟨c,hc,C,hC,h⟩
  have hvle := hmin (show t ∈ Icc A B ∩ E from ⟨⟨ht.1,ht.2.le.trans hv.1.2⟩,htE⟩)
  exact (not_le_of_gt ht.2) hvle

#print axioms projective_first_circuit_visit_deadline
/-- Absolute time of the first affordable unitary at or after A. -/
def firstCircuitVisit (H : selfAdjoint (Reg n)) (s : ℕ) (A : ℝ) : ℝ :=
  sInf {v : ℝ | A ≤ v ∧
    HasProjectiveCircuitApproximation n (1/10:ℝ) s (unitaryEvolution (H : Reg n) v)}

private theorem firstCircuitVisit_spec (H : selfAdjoint (Reg n)) (s : ℕ) (A : ℝ) :
    IsLeast {v : ℝ | A ≤ v ∧
      HasProjectiveCircuitApproximation n (1/10:ℝ) s (unitaryEvolution (H : Reg n) v)}
      (firstCircuitVisit H s A) ∧
    firstCircuitVisit H s A ≤ (|A|+1)*(100:ℝ)^(2^n-1) := by
  let e : (Fin n → Bool) ≃ Fin ((2^n-1)+1) := (Fintype.equivFin _).trans
    (finCongr (by simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
                  have h : 0 < (2:ℕ)^n := by positivity
                  omega))
  obtain ⟨v,hv,heasy,hgap⟩ := projective_first_circuit_visit_deadline e H A s
  have hmin : IsLeast {t : ℝ | A ≤ t ∧
      HasProjectiveCircuitApproximation n (1/10:ℝ) s (unitaryEvolution (H : Reg n) t)} v := by
    refine ⟨⟨hv.1,heasy⟩,?_⟩
    rintro t ⟨ht,c,hc,C,hC,hd⟩
    by_contra! h
    exact (not_lt_of_ge hd) (hgap t ⟨ht,h⟩ c hc C hC)
  rw [firstCircuitVisit,hmin.csInf_eq]
  exact ⟨hmin,hv.2⟩

/-- The length-W window contains a short circuit exactly when the attained
first entrance is at most W time units away. -/
theorem circuitWindowHits_eq_firstVisit (H : selfAdjoint (Reg n)) (s : ℕ) (W : ℝ) :
    circuitWindowHits (H : Reg n) s W =
      {u | firstCircuitVisit H s u ≤ u+W} := by
  ext u
  have hm := (firstCircuitVisit_spec H s u).1
  constructor
  · rintro ⟨t,ht,hc⟩
    exact (hm.2 ⟨ht.1,hc⟩).trans ht.2
  · intro h
    exact ⟨_,⟨hm.1.1,h⟩,hm.1.2⟩

/-- The first visit to the full short-circuit set has an explicit deterministic
deadline. Starts with a wait shorter than the doubly exponential hard-window
width have a doubly exponentially small upper density on the same Gaussian
path that permanently retains a two-query locality signal. -/
theorem gaussianPath_first_circuit_visit_distribution :
    ∀ᶠ L : ℕ in Filter.atTop,
    ∀ᵐ p ∂(centredProductGaussian
      (Fin (StaticLocalLaboratoryComplexityGrowthLaw.nearestNeighborPathLocalParameterCount L)) 1),
      let n := L*2
      let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
      let r := excursionGateBudget n
      let W := translatedExcursionWidth n ‖(H : Reg n)‖
      (∀ u : ℝ, u ≤ firstCircuitVisit H r u ∧
        HasProjectiveCircuitApproximation n (1/10:ℝ) r (unitaryEvolution (H : Reg n) (firstCircuitVisit H r u)) ∧
        firstCircuitVisit H r u ≤ (|u|+1)*(100:ℝ)^(2^n-1)) ∧
      (∃ S : ℝ, 0 ≤ S ∧ ∀ A T : ℝ, 0 ≤ T →
        (r+1:ℝ)^r * MeasureTheory.volume.real
          ({u | firstCircuitVisit H r u ≤ u+W} ∩ Icc A (A+T)) ≤ T+S) ∧
      RHTower.NearestNeighborPathPermanentLocalityHaarSeparation L p := by
  filter_upwards [gaussianPath_rare_circuitWindowHits_and_permanentLocality] with L hL
  filter_upwards [hL] with p hp
  refine ⟨fun u => ?_,?_,hp.2⟩
  · have hu := firstCircuitVisit_spec (RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p)
      (excursionGateBudget (L*2)) u
    exact ⟨hu.1.1.1,hu.1.1.2,hu.2⟩
  · simpa only [circuitWindowHits_eq_firstVisit] using hp.1

#print axioms gaussianPath_first_circuit_visit_distribution

/-- Differences inside a phase box are returns. Translating each color by
its earliest point in the closure covers the entire observation interval
with translates of its positive return times. -/
private theorem prefix_measure_of_coloring {ι : Type*} [Fintype ι]
    (B : Set ℝ) (hB : IsClosed B) (f : ℝ → ι)
    (h : ∀ x y, f x = f y → x-y ∈ B) (T : ℝ) (hT : 0 ≤ T) :
    T ≤ (Fintype.card ι : ℝ) * volume.real (B ∩ Icc 0 T) := by
  let X (i : ι) := Icc 0 T ∩ f ⁻¹' {i}
  let a (i : ι) := sInf (X i)
  let K := B ∩ Icc 0 T
  let G (i : ι) := (fun t : ℝ => t + -(a i)) ⁻¹' K
  let F (i : ι) := G i ∩ Icc 0 T
  have hcov : Icc 0 T ⊆ ⋃ i, F i := by
    intro t ht
    let i := f t
    have hx : t ∈ X i := ⟨ht,rfl⟩
    have hb : BddBelow (X i) := ⟨0,fun _ hu => hu.1.1⟩
    have hcl := csInf_mem_closure ⟨t,hx⟩ hb
    have hzero : 0 ≤ a i := le_csInf ⟨t,hx⟩ (fun _ hu => hu.1.1)
    have hle : a i ≤ t := csInf_le hb hx
    have hs : X i ⊆ (fun u : ℝ => t-u) ⁻¹' B := fun u hu => h t u (show f u = i from hu.2).symm
    have hmem := closure_minimal hs (hB.preimage (continuous_const.sub continuous_id)) hcl
    refine Set.mem_iUnion.mpr ⟨i,?_,ht⟩
    change t + -(a i) ∈ B ∩ Icc 0 T
    rw [← sub_eq_add_neg]
    exact ⟨hmem,sub_nonneg.mpr hle,(sub_le_self t hzero).trans ht.2⟩
  have hm : MeasurableSet K := hB.measurableSet.inter measurableSet_Icc
  have hG (i : ι) : volume (G i) = volume K :=
    (measurePreserving_add_right volume (-(a i))).measure_preimage hm.nullMeasurableSet
  have hK : volume K ≠ ⊤ := measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have hF (i : ι) : volume.real (F i) ≤ volume.real K := by
    have hv : volume.real (F i) ≤ volume.real (G i) :=
      measureReal_mono inter_subset_left (by rw [hG]; exact hK)
    simpa only [Measure.real,hG] using hv
  have hbound : (⋃ i, F i) ⊆ Icc 0 T := Set.iUnion_subset fun _ => inter_subset_right
  calc
    T = volume.real (Icc 0 T) := by rw [Real.volume_real_Icc_of_le hT,sub_zero]
    _ ≤ volume.real (⋃ i, F i) := measureReal_mono hcov (measure_ne_top_of_subset hbound measure_Icc_lt_top.ne)
    _ ≤ ∑ i, volume.real (F i) := measureReal_iUnion_fintype_le F
    _ ≤ ∑ _i : ι, volume.real K := Finset.sum_le_sum fun i _ => hF i
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, K]

/-- Fixed-error near-identity returns occupy at least one phase box's
fraction of every interval starting at zero, for every static generator. -/
theorem zero_gate_prefix_occupation (H : selfAdjoint (Reg n)) (T : ℝ) (hT : 0 ≤ T) :
    T ≤ (100:ℝ)^(2^n-1) * volume.real
      ({t | HasProjectiveCircuitApproximation n (1/10:ℝ) 0 (unitaryEvolution (H : Reg n) t)} ∩ Icc 0 T) := by
  let d := 2^n-1
  let e : (Fin n → Bool) ≃ Fin (d+1) := (Fintype.equivFin _).trans
    (finCongr (by simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
                  have hpos : 0 < (2:ℕ)^n := by positivity
                  dsimp [d]; omega))
  let E := H.2.isHermitian.eigenvalues
  let a := e.symm 0
  let z (t : ℝ) (i : Fin (d+1)) := t*(E (e.symm i)-E a)/(2*Real.pi)
  let f (t : ℝ) (j : Fin d) : Fin 100 :=
    ⟨boxIndex 100 (z t j.succ),boxIndex_lt (by norm_num) _⟩
  apply le_trans (prefix_measure_of_coloring _ (closed_physical_circuit_hits H 0 (1/10:ℝ)) f ?_ T hT)
  · simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,d,le_refl]
  intro u v huv
  let t := u-v
  refine ⟨anchorPhase E a t,by simp [anchorPhase,Complex.norm_exp],TwoQubitCircuit.one n,by rfl,?_⟩
  rw [TwoQubitCircuit.one_eval]
  change ‖unitaryEvolution (H : Reg n) t - anchorPhase E a t • (1:Reg n)‖ ≤ 1/10
  rw [l2_opNorm_unitaryEvolution_sub_anchorPhase H.2.isHermitian a t]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : 0 ≤ (1/10:ℝ))).mpr
  intro i
  let x := t*(E i-E a)
  have he : -(Complex.I * ((t:ℂ) * ((E i:ℂ)-(E a:ℂ)))) = -(Complex.I*(x:ℂ)) := by
    dsimp [x]; push_cast; rfl
  change ‖Complex.exp (-(Complex.I*((t:ℂ)*((E i:ℂ)-(E a:ℂ))))) - 1‖ ≤ 1/10
  rw [he]
  refine (chord_le_of_turns_close x 99 ?_).trans (by norm_num; linarith [Real.pi_lt_four])
  dsimp only [x]
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  refine Fin.cases ?_ (fun j => ?_) j
  · refine ⟨0,?_⟩
    simp [a]
  · have hb := abs_fract_sub_lt_of_boxIndex_eq (Q := 100) (by norm_num)
      (congrArg Fin.val (congrFun huv j))
    refine ⟨⌊z u j.succ⌋ - ⌊z v j.succ⌋,?_⟩
    change |t*(E (e.symm j.succ)-E a)/(2*Real.pi) - _| < _
    rw [show t*(E (e.symm j.succ)-E a)/(2*Real.pi) = z u j.succ - z v j.succ by dsimp [z,t]; ring]
    rw [Int.cast_sub]
    have hz (s : ℝ) := Int.floor_add_fract (z s j.succ)
    convert hb using 1
    · congr 1
      linarith only [hz u,hz v]
    · norm_num

#print axioms zero_gate_prefix_occupation

/-- Every budget from zero to the near-Hilbert threshold has doubly
exponentially small occupation bounded on both sides for one fixed draw. -/
theorem gaussianPath_two_sided_short_circuit_occupation :
    ∀ᶠ L : ℕ in Filter.atTop,
    ∀ᵐ p ∂(centredProductGaussian
      (Fin (StaticLocalLaboratoryComplexityGrowthLaw.nearestNeighborPathLocalParameterCount L)) 1),
      let n := L*2
      let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
      let r := excursionGateBudget n
      (∃ S : ℝ, 0 ≤ S ∧ ∀ s ≤ r, ∀ T : ℝ, 0 ≤ T →
        let V := volume.real ({t | HasProjectiveCircuitApproximation n (1/10:ℝ) s
          (unitaryEvolution (H : Reg n) t)} ∩ Icc 0 T)
        T ≤ (100:ℝ)^(2^n-1)*V ∧ (r+1:ℝ)^r*V ≤ T+S) ∧
      RHTower.NearestNeighborPathPermanentLocalityHaarSeparation L p := by
  filter_upwards [gaussianPath_rare_circuitWindowHits_and_permanentLocality] with L hL
  filter_upwards [hL] with p hp
  obtain ⟨⟨S,hS,hocc⟩,hloc⟩ := hp
  refine ⟨⟨S,hS,fun s hs T hT => ?_⟩,hloc⟩
  let n := L*2
  let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
  let r := excursionGateBudget n
  let W := translatedExcursionWidth n ‖(H : Reg n)‖
  let B (j : ℕ) := {t | HasProjectiveCircuitApproximation n (1/10:ℝ) j (unitaryEvolution (H : Reg n) t)}
  have hfin {E : Set ℝ} : volume (E ∩ Icc 0 T) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have hlow : B 0 ⊆ B s := by
    rintro t ⟨c,hc,C,hC,he⟩; exact ⟨c,hc,C,by omega,he⟩
  have hW : 0 ≤ W := by dsimp [W,translatedExcursionWidth]; positivity
  have hhigh : B s ⊆ circuitWindowHits (H : Reg n) r W := by
    rintro t ⟨c,hc,C,hC,he⟩
    exact ⟨t,⟨le_rfl,le_add_of_nonneg_right hW⟩,c,hc,C,hC.trans hs,he⟩
  have hlo := measureReal_mono (μ := volume) (inter_subset_inter_left (Icc 0 T) hlow) hfin
  have hhi := measureReal_mono (μ := volume) (inter_subset_inter_left (Icc 0 T) hhigh) hfin
  constructor
  · exact (zero_gate_prefix_occupation H T hT).trans (mul_le_mul_of_nonneg_left hlo (by positivity))
  · apply (mul_le_mul_of_nonneg_left hhi (by positivity : 0 ≤ (r+1:ℝ)^r)).trans
    simpa only [zero_add] using hocc 0 T hT

#print axioms gaussianPath_two_sided_short_circuit_occupation

end
end GaloisForLFunctions.HTGeometry
