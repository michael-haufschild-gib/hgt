import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeRadialMollification

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate
namespace RHTower.D4BMNativeResponse
open D4BMJointWave D4BMModularCore GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem norm_toLp_sq {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {f : X → E} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  exact hf.coeFn_toLp.mono (fun _ h => congrArg (fun a => ‖a‖^2) h)

private theorem slot_norm_sq (i : Fin 3) (f : ℝ → energyDomain) (hf : MemLp f 2 radialMeasure) :
    ‖radialFamilySlot i (hf.toLp f)‖^2 = ∫ x, ‖angularEnergySlot i (f x)‖^2 ∂radialMeasure := by
  change ‖bochnerL2ProductEquiv ((angularEnergySlot i).compLp (hf.toLp f))‖^2 = _
  rw [bochnerL2ProductEquiv.norm_map,_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [(angularEnergySlot i).coeFn_compLp (hf.toLp f),hf.coeFn_toLp] with x h0 h1
  rw [h0,h1]

private theorem cutoff_value_mem (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) :
    MemLp (nativeTimePrimitiveAngularEnergy q s amplitude t n) 2 radialMeasure :=
  (nativeTimePrimitiveAngularEnergy_continuous q s amplitude t n).memLp_of_hasCompactSupport
    (nativeTimePrimitiveAngularEnergy_compact q s amplitude t n)

private theorem cutoff_radial_mem (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) :
    MemLp (deriv (fun x => embedding (nativeTimePrimitiveAngularEnergy q s amplitude t n x))) 2 radialMeasure :=
  ((contDiff_one_iff_deriv.mp (nativeTimePrimitiveAngularEnergy_value_contDiff q s amplitude t n)).2).memLp_of_hasCompactSupport
    (((nativeTimePrimitiveAngularEnergy_compact q s amplitude t n).comp_left (map_zero embedding)).deriv)

private theorem cutoff_weight_mem (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) :
    MemLp (fun x => angularWeight x • nativeTimePrimitiveAngularEnergy q s amplitude t n x) 2 radialMeasure := by
  apply (angularWeight_smooth.continuous.smul (nativeTimePrimitiveAngularEnergy_continuous q s amplitude t n)).memLp_of_hasCompactSupport
  apply (nativeTimePrimitiveAngularEnergy_compact q s amplitude t n).mono
  intro x hx hz
  apply hx
  change angularWeight x • nativeTimePrimitiveAngularEnergy q s amplitude t n x = 0
  rw [hz,smul_zero]

private theorem native_graph_radial_norm (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) :
    ‖nativeCuspJointGraph q s amplitude t n 1‖^2 =
      ∫ x, ∫ z, nativeJointRadialCutoffEnergy q s amplitude t n (x,z)
        ∂D4BMModularCore.measure ∂radialMeasure := by
  change ‖bochnerL2ProductEquiv ((cutoff_radial_mem q s amplitude t n).toLp
    (deriv (fun x => embedding (nativeTimePrimitiveAngularEnergy q s amplitude t n x))))‖^2 = _
  rw [bochnerL2ProductEquiv.norm_map,norm_toLp_sq]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change ‖deriv (fun y => embedding (nativeTimePrimitiveAngularEnergy q s amplitude t n y)) x‖^2 = _
  rw [(nativeTimePrimitiveAngularEnergy_value_hasDerivAt q s amplitude t n x).deriv]
  rw [nativeTimePrimitiveAngularRadial,norm_toLp_sq]
  rfl

private theorem native_graph_value_norm (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) :
    ‖nativeCuspJointGraph q s amplitude t n 0‖^2 =
      ∫ x, ∫ z, ‖modularCuspCutoff ((n:ℝ)+1) z*nativeJointTimePrimitiveField q s amplitude t (x,z)‖^2
        ∂D4BMModularCore.measure ∂radialMeasure := by
  change ‖radialFamilySlot 0 ((cutoff_value_mem q s amplitude t n).toLp
    (nativeTimePrimitiveAngularEnergy q s amplitude t n))‖^2 = _
  rw [slot_norm_sq]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change ‖fieldVector (nativeTimePrimitiveCutoff q s amplitude t x n 0)‖^2 = _
  rw [fieldVector,norm_toLp_sq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
  change ‖modularCuspCutoff ((n:ℝ)+1) z^(0+1)*globalNativeTimePrimitive q s amplitude t x z‖^2 = _
  rw [(globalNativeTimePrimitive_germ q s amplitude t x z hz).eq_of_nhds]
  simp only [Nat.zero_add,pow_one,nativeJointTimePrimitiveField]

private theorem native_graph_angular_norm (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (i : Fin 2) :
    ‖nativeCuspJointGraph q s amplitude t n i.succ.succ‖^2 =
      ∫ x, ∫ z, ‖weightedDeriv (direction i) (nativeTimePrimitiveCutoff q s amplitude t x n 0).field z‖^2/
        Real.cosh x^2 ∂D4BMModularCore.measure ∂radialMeasure := by
  have hi (x : ℝ) :
      angularEnergySlot i.succ (nativeTimePrimitiveAngularEnergy q s amplitude t n x) =
      derivativeVector (nativeTimePrimitiveCutoff q s amplitude t x n 0) (direction i) := by
    fin_cases i <;> rfl
  have hslot : nativeCuspJointGraph q s amplitude t n i.succ.succ =
      radialFamilySlot i.succ ((cutoff_weight_mem q s amplitude t n).toLp
        (fun x => angularWeight x • nativeTimePrimitiveAngularEnergy q s amplitude t n x)) := by
    fin_cases i <;> rfl
  rw [hslot,slot_norm_sq]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change ‖angularEnergySlot i.succ (angularWeight x • nativeTimePrimitiveAngularEnergy q s amplitude t n x)‖^2 = _
  rw [map_smul,hi,norm_smul,mul_pow,derivativeVector,norm_toLp_sq,← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  rw [angularWeight,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_pos (Real.cosh_pos x)]
  field_simp

private theorem native_graph_value_bound (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) :
    ‖nativeCuspJointGraph q s amplitude t n 0‖^2 ≤
      ∫ p, ‖nativeJointTimePrimitiveField q s amplitude t p‖^2
        ∂radialMeasure.prod D4BMModularCore.measure := by
  have hm := nativeJointTimePrimitiveField_memLp q s amplitude t
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  rw [native_graph_value_norm,integral_prod _ hi]
  apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _)))
    hi.integral_prod_left
  filter_upwards [hi.prod_right_ae] with x hx
  apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => sq_nonneg _)) hx
  apply Eventually.of_forall
  intro z
  dsimp only
  rw [norm_mul]
  have he := mul_le_mul_of_nonneg_right (modularCuspCutoff_norm_le_one ((n:ℝ)+1) z)
    (norm_nonneg (nativeJointTimePrimitiveField q s amplitude t (x,z)))
  simpa only [one_mul] using pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) he 2

private theorem native_graph_angular_bound (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (i : Fin 2) :
    ‖nativeCuspJointGraph q s amplitude t n i.succ.succ‖^2 ≤
      ∫ p, nativeJointAngularCutoffEnergy q s amplitude t n p
        ∂radialMeasure.prod D4BMModularCore.measure := by
  have hi := (nativeTimePrimitive_compact_joint_energy q s amplitude t n).2.1
  rw [native_graph_angular_norm,integral_prod _ hi]
  apply integral_mono_of_nonneg
    (Eventually.of_forall (fun _ => integral_nonneg (fun _ => div_nonneg (sq_nonneg _) (sq_nonneg _))))
    hi.integral_prod_left
  filter_upwards [hi.prod_right_ae] with x hx
  apply integral_mono_of_nonneg
    (Eventually.of_forall (fun _ => div_nonneg (sq_nonneg _) (sq_nonneg _))) hx
  apply Eventually.of_forall
  intro z
  dsimp only
  unfold nativeJointAngularCutoffEnergy
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 2))) =>
    sq_nonneg (‖weightedDeriv (direction j) (nativeTimePrimitiveCutoff q s amplitude t x n 0).field z‖))
    (Finset.mem_univ i)

/-- The actual admitted cutoff graphs are controlled by the original native mass and gradient energy. -/
theorem nativeCuspJointGraph_norm_sq_bound (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) :
    ‖nativeCuspJointGraph q s amplitude t n‖^2 ≤
      (∫ p, ‖nativeJointTimePrimitiveField q s amplitude t p‖^2
        ∂radialMeasure.prod D4BMModularCore.measure)+
      2*(∫ p, nativeJointRadialCutoffEnergy q s amplitude t n p+
        nativeJointAngularCutoffEnergy q s amplitude t n p
        ∂radialMeasure.prod D4BMModularCore.measure) := by
  have hr := (nativeTimePrimitive_compact_joint_energy q s amplitude t n).1
  have ha := (nativeTimePrimitive_compact_joint_energy q s amplitude t n).2.1
  have h0 := native_graph_value_bound q s amplitude t n
  have h1 := native_graph_radial_norm q s amplitude t n
  rw [← integral_prod _ hr] at h1
  have h2 := native_graph_angular_bound q s amplitude t n 0
  have h3 := native_graph_angular_bound q s amplitude t n 1
  rw [PiLp.norm_sq_eq_of_L2,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,
    Fin.sum_univ_one,integral_add hr ha]
  change ‖nativeCuspJointGraph q s amplitude t n 2‖^2 ≤ _ at h2
  change ‖nativeCuspJointGraph q s amplitude t n 3‖^2 ≤ _ at h3
  change ‖nativeCuspJointGraph q s amplitude t n 0‖^2+
    (‖nativeCuspJointGraph q s amplitude t n 1‖^2+
    (‖nativeCuspJointGraph q s amplitude t n 2‖^2+‖nativeCuspJointGraph q s amplitude t n 3‖^2)) ≤ _
  have hn : 0 ≤ ∫ p, nativeJointRadialCutoffEnergy q s amplitude t n p
      ∂radialMeasure.prod D4BMModularCore.measure := integral_nonneg (fun _ => sq_nonneg _)
  linarith

/-- The original form norms of all actual cusp-cutoff graphs have one finite bound. -/
theorem nativeCuspJointGraph_bounded (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    ∃ M : ℝ, ∀ n : ℕ, ‖nativeCuspJointGraph q s amplitude t n‖ ≤ M := by
  obtain ⟨C,hC⟩ := (nativeTimePrimitive_cutoff_energy_limit q s amplitude t).bddAbove_range
  let D := (∫ p, ‖nativeJointTimePrimitiveField q s amplitude t p‖^2
      ∂radialMeasure.prod D4BMModularCore.measure)+2*C
  refine ⟨max D 0+1,?_⟩
  intro n
  have he := nativeCuspJointGraph_norm_sq_bound q s amplitude t n
  have hc := hC (Set.mem_range_self n)
  have hd : ‖nativeCuspJointGraph q s amplitude t n‖^2 ≤ D := by
    dsimp only [D]
    linarith
  nlinarith [le_max_left D 0,le_max_right D 0,
    sq_nonneg (‖nativeCuspJointGraph q s amplitude t n‖-1/2)]

end
end RHTower.D4BMNativeResponse
