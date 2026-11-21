import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.GaussianLaw

/-! # Circuit targets allowed to change at every harmonic -/
open Filter Set MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.HarmonicRuns
noncomputable section
open SharpOccupation

private theorem difference_visit {n : ℕ} (H : selfAdjoint (Register n)) (W : Register n)
    {s t η : ℝ} {c d : ℂ} (hc : ‖c‖=1) (hd : ‖d‖=1)
    (hs : ‖unitaryEvolution H.val s-c • W‖ ≤ η) (ht : ‖unitaryEvolution H.val t-d • W‖ ≤ η) :
    HasProjectiveCircuitApproximation n (2*η) 0 (unitaryEvolution H.val (s-t)) := by
  let z := c/d
  have hz : ‖z‖=1 := by rw [show z=c/d from rfl,norm_div,hc,hd,div_one]
  have hzd : z*d=c := div_mul_cancel₀ _ (norm_ne_zero_iff.mp (hd.trans_ne one_ne_zero))
  have hdif : ‖c • W-z • unitaryEvolution H.val t‖ ≤ η := by
    rw [←hzd,←smul_smul,←smul_sub,norm_smul,hz,one_mul,norm_sub_rev]
    exact ht
  refine ⟨z,hz,TwoQubitCircuit.one n,le_rfl,?_⟩
  rw [TwoQubitCircuit.one_eval]
  change ‖unitaryEvolution H.val (s-t)-z • (1 : Register n)‖ ≤ _
  rw [←CStarRing.norm_mul_mem_unitary _ (unitaryEvolution_mem_unitary H.2 t),
    Matrix.sub_mul,unitaryEvolution_sub_mul H s t,Matrix.smul_mul,one_mul]
  exact (norm_sub_le_norm_sub_add_norm_sub _ (c • W) _).trans
    ((add_le_add hs hdif).trans_eq (by ring))

/-- Steps satisfying an ordered list of projective unitary tests. -/
def itinerary {n m : ℕ} (H : selfAdjoint (Register n))
    (W : Fin m → Matrix.unitaryGroup (Fin n → Bool) ℂ) (η : ℝ) : Set ℝ :=
  {t | ∀ i : Fin m, ∃ c : ℂ, ‖c‖=1 ∧
    ‖unitaryEvolution H.val (((i.val:ℝ)+1)*t)-c • (W i : Register n)‖ ≤ η}

/-- Two steps realizing the same list of targets differ by a single
empty-circuit return at the angular tolerance divided by the list length. -/
theorem itinerary_difference {n m : ℕ} (H : selfAdjoint (Register n)) (hm : 0 < m)
    (W : Fin m → Matrix.unitaryGroup (Fin n → Bool) ℂ) {η x s t : ℝ}
    (hx : 0 ≤ x) (hshort : 3*x < 1) (he : 2*η ≤ zeroGateArcTolerance x)
    (hs : s ∈ itinerary H W η) (ht : t ∈ itinerary H W η) :
    s-t ∈ zeroGateReturnSet H (x/(m:ℝ)) := by
  rw [←runSet_eq H hx hshort m hm]
  intro k hk
  cases k with
  | zero =>
    refine ⟨1,by simp,TwoQubitCircuit.one n,le_rfl,?_⟩
    simp only [Nat.cast_zero,zero_mul,unitaryEvolution,zero_smul,NormedSpace.exp_zero,one_smul,
      TwoQubitCircuit.one_eval,Unitary.val_one,sub_self,norm_zero]
    have hpos := strictMonoOn_zeroGateArcTolerance.monotoneOn (by norm_num : (0:ℝ) ∈ Icc 0 (1/2))
      ⟨hx,by linarith only [hshort]⟩ hx
    simpa only [zeroGateArcTolerance,mul_zero,zero_div,Real.sin_zero] using hpos
  | succ k =>
    let i : Fin m := ⟨k,hk⟩
    obtain ⟨c,hc,hs'⟩ := hs i
    obtain ⟨d,hd,ht'⟩ := ht i
    obtain ⟨z,hz,C,hC,herr⟩ := difference_visit H _ hc hd hs' ht'
    refine ⟨z,hz,C,hC,?_⟩
    simpa only [i,Nat.cast_add_one,mul_sub] using herr.trans he

/-- All steps with an s-gate visit at each of the first m harmonics. -/
def circuitRunSet {n : ℕ} (H : selfAdjoint (Register n)) (s m : ℕ) (ε : ℝ) : Set ℝ :=
  {t | ∀ i : Fin m, ((i.val:ℝ)+1)*t ∈ visitSet H s ε}

private theorem translated_return_density {n : ℕ} (H : selfAdjoint (Register n))
    (hi : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) (r : Icc (0:ℝ) (1/2)) (a u : ℝ) :
    Tendsto (fun T => volume.real (((fun t : ℝ => t-u) ⁻¹' zeroGateReturnSet H r) ∩ Icc a T)/(T-a))
      atTop (𝓝 (zeroGateArcDensity (2^n) r)) := by
  let Z := zeroGateReturnSet H r
  have hZ : MeasurableSet Z := (isClosed_le (orbitCircuitDistance_lipschitz H 0).continuous continuous_const).measurableSet
  have hl := (maximallyProjective_zeroGateOccupation_from_start H hi r (a-u)).comp
    (tendsto_atTop_add_const_right atTop (-u) tendsto_id)
  apply hl.congr
  intro T
  have he : ((fun t : ℝ => t-u) ⁻¹' Z) ∩ Icc a T =
      (fun t : ℝ => t+(-u)) ⁻¹' (Z ∩ Icc (a-u) (T-u)) := by
    ext t
    simp only [mem_preimage,mem_inter_iff,mem_Icc,sub_eq_add_neg,add_le_add_iff_right]
  have hv := (measurePreserving_add_right volume (-u)).measureReal_preimage
    (hZ.inter measurableSet_Icc).nullMeasurableSet
  change volume.real (Z ∩ Icc (a-u) (T+-u))/((T+-u)-(a-u)) = volume.real _/(T-a)
  rw [←sub_eq_add_neg,sub_sub_sub_cancel_right,he,hv]

/-- The net cardinality is raised to m because the circuit can change at
every harmonic. The exponent D−1 on the shrinking angular tolerance comes
from the relative energy phases of a single fixed Hamiltonian. -/
theorem circuit_run_bound {n : ℕ} (H : selfAdjoint (Register n))
    (hi : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) (s m : ℕ) (hm : 0 < m)
    {ε δ x : ℝ} (hδ : 0 < δ) (hx : 0 ≤ x) (hshort : 3*x < 1)
    (he : 2*(ε+δ) ≤ zeroGateArcTolerance x) (a b : ℝ)
    (hb : (((s:ℝ)+1)*((((n:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32)^s)^m *
      zeroGateArcDensity (2^n) (x/(m:ℝ)) < b) :
    ∀ᶠ T : ℝ in atTop, volume.real (circuitRunSet H s m ε ∩ Icc a T)/(T-a) < b := by
  classical
  obtain ⟨F,hcover,hcard⟩ := exists_budget_net n s δ hδ
  let word (f : Fin m → F) := fun i => (f i).val
  let A (f : Fin m → F) := itinerary H (word f) (ε+δ)
  let Z := zeroGateReturnSet H (x/(m:ℝ))
  have htranslate (f : Fin m → F) : ∃ u : ℝ, A f ⊆ (fun t : ℝ => t-u) ⁻¹' Z := by
    by_cases hn : (A f).Nonempty
    · obtain ⟨u,hu⟩ := hn
      exact ⟨u,fun _ ht => itinerary_difference H hm _ hx hshort he ht hu⟩
    · exact ⟨0,fun t ht => (hn ⟨t,ht⟩).elim⟩
  choose u hu using htranslate
  let B (f : Fin m → F) := (fun t : ℝ => t-u f) ⁻¹' Z
  have hsub : circuitRunSet H s m ε ⊆ ⋃ f, B f := by
    intro t ht
    have hsel (i : Fin m) : ∃ w : F, ∃ c : ℂ, ‖c‖=1 ∧
        ‖unitaryEvolution H.val (((i.val:ℝ)+1)*t)-c • (w.val:Register n)‖ ≤ ε+δ := by
      obtain ⟨c,hc,C,hC,herr⟩ := ht i
      obtain ⟨w,hw,hclose⟩ := hcover C hC
      refine ⟨⟨w,hw⟩,c,hc,(norm_sub_le_norm_sub_add_norm_sub _ (c • (C.eval : Register n)) _).trans
        (add_le_add herr ?_)⟩
      rwa [←smul_sub,norm_smul,hc,one_mul]
    choose f c hc hclose using hsel
    exact mem_iUnion.mpr ⟨f,hu f (fun i => ⟨c i,hc i,hclose i⟩)⟩
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  let r : Icc (0:ℝ) (1/2) := ⟨x/(m:ℝ),div_nonneg hx (Nat.cast_nonneg _),
    (div_le_self hx hm1).trans (by linarith only [hshort])⟩
  let p := zeroGateArcDensity (2^n) r
  have ht (f : Fin m → F) := translated_return_density H hi r a (u f)
  have hsum : Tendsto (fun T => ∑ f : Fin m → F, volume.real (B f ∩ Icc a T)/(T-a)) atTop
      (𝓝 ((F.card:ℝ)^m*p)) := by
    simpa [p,r,B,Z] using tendsto_finsetSum Finset.univ (fun f _ => ht f)
  have hp : 0 ≤ p := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg r.2.1 _)
  have hh := hsum.eventually_lt_const ((mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard m) hp).trans_lt hb)
  filter_upwards [hh,eventually_gt_atTop a] with T hT hTa
  apply lt_of_le_of_lt _ hT
  rw [←Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hTa.le)
  let C (f : Fin m → F) := B f ∩ Icc a T
  have hfinite : (⋃ f, C f) ⊆ Icc a T := iUnion_subset fun _ => inter_subset_right
  apply (measureReal_mono (s₂ := ⋃ f, C f) _ (measure_ne_top_of_subset hfinite measure_Icc_lt_top.ne)).trans
    (measureReal_iUnion_fintype_le C)
  rintro t ⟨ht,hT⟩
  obtain ⟨f,hf⟩ := mem_iUnion.mp (hsub ht)
  exact mem_iUnion.mpr ⟨f,hf,hT⟩

/-- On a single draw the changing-circuit run bound holds on every prefix,
for all origins and all finite run lengths. -/
theorem gaussian_circuit_run_bound :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let n := k+3
      let H : selfAdjoint (Register n) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ s m : ℕ, 0 < m → ∀ ε δ x : ℝ, 0 < δ → 0 ≤ x → 3*x < 1 →
        2*(ε+δ) ≤ zeroGateArcTolerance x → ∀ a b : ℝ,
        (((s:ℝ)+1)*((((n:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32)^s)^m *
          zeroGateArcDensity (2^n) (x/(m:ℝ)) < b →
        ∀ᶠ T : ℝ in atTop, volume.real (circuitRunSet H s m ε ∩ Icc a T)/(T-a) < b := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro k n H s m hm ε δ x hδ hx hshort he a b hb
  exact circuit_run_bound H (hω k) s m hm hδ hx hshort he a b hb

#print axioms gaussian_circuit_run_bound
end
end GaloisForLFunctions.HTGeometry.HarmonicRuns
