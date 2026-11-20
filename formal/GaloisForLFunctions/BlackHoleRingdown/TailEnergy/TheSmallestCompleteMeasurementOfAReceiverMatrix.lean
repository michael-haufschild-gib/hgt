import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.RecoveringEveryReceiverPairAlongOneSpiral
import GaloisForLFunctions.HTGeometry.ComplexIntegralGram
import GaloisForLFunctions.HTGeometry.ConstitutivePositiveConeMidpointRecovery
import GaloisForLFunctions.HTGeometry.MatrixQuadraticFormDetermination

/-!
# Which receiver matrices occur, and how many readings determine them?

After every prescribed late cutoff, compact incident pulses realize the
entire cone of positive semidefinite complex matrices. Thus n² scalar
energy readings are necessary even for a nonlinear reconstruction from
fixed mixtures of n incident channels. The spiral experiment attains this
number on the actual receiver.
-/

noncomputable section
open Complex Matrix MeasureTheory Finset Set
open GaloisForLFunctions.HTGeometry
open scoped MatrixOrder ComplexOrder ComplexConjugate
namespace GaloisForLFunctions.BlackHoleRingdown

def receiverWindowMatrix {n : ℕ} (f : Fin n → CompactPulse) (W : Set ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => reflectedWindowGram (f i) (f j) W

theorem receiverWindowMatrix_posSemidef {n : ℕ} (f : Fin n → CompactPulse) (W : Set ℝ) :
    (receiverWindowMatrix f W).PosSemidef :=
  complexFeatureGram_posSemidef (volume.restrict W) (fun i => pulseReflected (f i))
    (fun i j => (integrable_pulseReflected_mul_conj (f i) (f j)).integrableOn)

private theorem matrix_mixture_energy {n : ℕ} (f : Fin n → CompactPulse) (W : Set ℝ) (x : Fin n → ℂ) :
    star x ⬝ᵥ (receiverWindowMatrix f W).mulVec x =
      (reflectedWindowEnergy (mixedPulse univ (star x) f) W : ℂ) := by
  rw [mixed_window_energy_gram]
  simp only [dotProduct,mulVec,receiverWindowMatrix,Finset.mul_sum,Pi.star_apply,
    Complex.star_def,Complex.conj_conj]
  apply sum_congr rfl
  intro i _
  exact sum_congr rfl fun j _ => by ring

/-- Changing the incident channels acts by congruence on every window. -/
theorem mixed_receiver_matrix {m n : ℕ} (f : Fin n → CompactPulse) (W : Set ℝ)
    (A : Matrix (Fin m) (Fin n) ℂ) :
    receiverWindowMatrix (fun i => mixedPulse univ (A i) f) W =
      A*receiverWindowMatrix f W*Aᴴ := by
  ext i j
  let F := fun k l t => pulseReflected (f k) t*conj (pulseReflected (f l) t)
  have hint (k l : Fin n) : IntegrableOn (fun t => (A i k*conj (A j l))*F k l t) W :=
    ((integrable_pulseReflected_mul_conj (f k) (f l)).const_mul _).integrableOn
  have hpoint (t : ℝ) : pulseReflected (mixedPulse univ (A i) f) t*
      conj (pulseReflected (mixedPulse univ (A j) f) t)=∑ k, ∑ l, (A i k*conj (A j l))*F k l t := by
    simp only [pulseReflected_mixedPulse,map_sum,Finset.sum_mul_sum,map_mul,F]
    exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
  change (∫ t in W, pulseReflected (mixedPulse univ (A i) f) t*
      conj (pulseReflected (mixedPulse univ (A j) f) t))=_
  simp_rw [hpoint]
  rw [integral_finsetSum univ (fun k _ => integrable_finsetSum univ (fun l _ => hint k l))]
  simp_rw [integral_finsetSum univ (fun l _ => hint _ l),integral_const_mul]
  simp only [Matrix.mul_apply,Finset.sum_mul,conjTranspose_apply,Complex.star_def]
  rw [sum_comm]
  exact sum_congr rfl fun l _ => sum_congr rfl fun k _ => by
    change (A i k*conj (A j l))*reflectedWindowGram (f k) (f l) W=_
    unfold receiverWindowMatrix
    ring

private def separatedPulse {n : ℕ} (j : Fin n) :=
  CompactPulse.delay (j.val:ℝ) (scaledBumpPulse 1 zero_lt_one)

private theorem separated_at_center {n : ℕ} (i j : Fin n) :
    separatedPulse j (i.val:ℝ)=if j=i then 1 else 0 := by
  change scaledBumpPulse 1 zero_lt_one ((i.val:ℝ)-j.val)=_
  rcases eq_or_ne j i with rfl | hj
  · rw [if_pos rfl,sub_self]
    change ((scaledBumpData 1 zero_lt_one (0:ℝ):ℝ):ℂ)=1
    rw [(scaledBumpData 1 zero_lt_one).one_of_mem_closedBall
      (Metric.mem_closedBall_self (scaledBumpData 1 zero_lt_one).rIn_pos.le),Complex.ofReal_one]
  · rw [if_neg hj]
    apply scaledBumpPulse_eq_zero_of_le
    have hne : j.val≠i.val := fun h => hj (Fin.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · have hb : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast Nat.succ_le_of_lt h
      exact (by linarith only [hb] : 1≤(i.val:ℝ)-j.val).trans (le_abs_self _)
    · have hb : (i.val:ℝ)+1≤j.val := by exact_mod_cast Nat.succ_le_of_lt h
      exact (by linarith only [hb] : 1≤ -((i.val:ℝ)-j.val)).trans (neg_le_abs _)

private theorem separated_tail_posDef (n : ℕ) (T : ℝ) :
    (receiverWindowMatrix (@separatedPulse n) (Ioi T)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (receiverWindowMatrix_posSemidef _ _).isHermitian fun x hx => ?_
  rw [matrix_mixture_energy]
  apply Complex.zero_lt_real.mpr
  apply tailEnergy_pos
  by_contra! h
  apply hx
  funext i
  have hi := h (i.val:ℝ)
  simp only [mixedPulse_apply,separated_at_center,mul_ite,mul_one,mul_zero,sum_ite_eq',Finset.mem_univ,if_true,
    Pi.star_apply,star_eq_zero] at hi
  exact hi

/-- Every late cutoff admits a physically orthonormal family in any
finite dimension. Whitening mixes only translates of a single compact bump. -/
theorem exists_orthonormal_tail_pulses (n : ℕ) (T : ℝ) :
    ∃ f : Fin n → CompactPulse, receiverWindowMatrix f (Ioi T)=1 := by
  let B := receiverWindowMatrix (@separatedPulse n) (Ioi T)
  let S := CFC.sqrt B
  have hB : B.PosDef := separated_tail_posDef n T
  have hS : S.PosDef := positiveMatrixSqrt_posDef hB
  have hu := (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  refine ⟨fun j => mixedPulse univ (S⁻¹ j) (@separatedPulse n),?_⟩
  rw [mixed_receiver_matrix]
  change S⁻¹*B*(S⁻¹)ᴴ=1
  rw [hS.isHermitian.inv.eq,←positiveMatrixSqrt_mul_self hB]
  change S⁻¹*(S*S)*S⁻¹=1
  rw [←mul_assoc S⁻¹ S S,Matrix.nonsing_inv_mul S hu,one_mul,Matrix.mul_nonsing_inv S hu]

/-- Exactly the positive semidefinite matrices occur as Gram matrices
of compact pulses after any prescribed cutoff. -/
theorem realizable_tail_matrix_iff_posSemidef {n : ℕ} (T : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (∃ f : Fin n → CompactPulse, receiverWindowMatrix f (Ioi T)=A) ↔ A.PosSemidef := by
  constructor
  · rintro ⟨f,rfl⟩
    exact receiverWindowMatrix_posSemidef f _
  · intro hA
    obtain ⟨f,hf⟩ := exists_orthonormal_tail_pulses n T
    let S := CFC.sqrt A
    have hS : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
    refine ⟨fun i => mixedPulse univ (S i) f,?_⟩
    rw [mixed_receiver_matrix,hf,mul_one,hS.eq]
    exact CFC.sqrt_mul_sqrt_self A (ha:=hA.nonneg)

private def probeMatrix {d n : ℕ} (c : Fin d → Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (Fin d → ℂ) where
  toFun A k := ∑ i, ∑ j, A i j*(c k i*conj (c k j))
  map_add' A B := by
    funext k
    simp only [Matrix.add_apply,add_mul,sum_add_distrib,Pi.add_apply]
  map_smul' z A := by
    funext k
    simp only [Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum,mul_assoc]

private theorem probe_conjTranspose {d n : ℕ} (c : Fin d → Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (k : Fin d) :
    probeMatrix c Aᴴ k=conj (probeMatrix c A k) := by
  have form (B : Matrix (Fin n) (Fin n) ℂ) :
      probeMatrix c B k=star (star (c k)) ⬝ᵥ B.mulVec (star (c k)) := by
    simp only [probeMatrix,LinearMap.coe_mk,AddHom.coe_mk,star_star,dotProduct,mulVec,
      Finset.mul_sum,Pi.star_apply,Complex.star_def,Complex.conj_conj]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  rw [form,matrixQuadraticForm_conjTranspose,form] <;> rfl

private theorem blind_hermitian_direction {d n : ℕ} (hd : d<n^2) (c : Fin d → Fin n → ℂ) :
    ∃ H : Matrix (Fin n) (Fin n) ℂ, H≠0 ∧ H.IsHermitian ∧ probeMatrix c H=0 := by
  let L := probeMatrix c
  have hk : ∃ Z : Matrix (Fin n) (Fin n) ℂ, Z≠0 ∧ L Z=0 := by
    by_contra! h
    have hinj : Function.Injective L := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr
      (fun X hX => by by_contra hn; exact h X hn hX))
    have dim := LinearMap.finrank_le_finrank_of_injective hinj
    exact hd.not_ge (by simpa only [Module.finrank_matrix,Module.finrank_fintype_fun_eq_card,
      Module.finrank_self,Fintype.card_fin,mul_one,sq] using dim)
  obtain ⟨Z,hZ,hL⟩ := hk
  have hadj : L Zᴴ=0 := by
    funext k
    rw [show L Zᴴ k=conj (L Z k) from probe_conjTranspose c Z k,hL]
    simp
  by_cases h : Z+Zᴴ=0
  · have he : Zᴴ= -Z := by
      calc Zᴴ = (Z+Zᴴ)-Z := by abel
           _ = -Z := by rw [h,zero_sub]
    refine ⟨I • Z,smul_ne_zero I_ne_zero hZ,?_,by rw [map_smul,hL,smul_zero]⟩
    change (I • Z)ᴴ=I • Z
    rw [conjTranspose_smul,he,Complex.star_def,Complex.conj_I,neg_smul,smul_neg,neg_neg]
  · exact ⟨Z+Zᴴ,h,by simp only [Matrix.IsHermitian,conjTranspose_add,conjTranspose_conjTranspose,add_comm],
      by rw [map_add,hL,hadj,add_zero]⟩

/-- Below n² measurements, two actual compact pulse families have the
same readings for any fixed mixing menu and different late Gram matrices.
This obstruction applies to arbitrary recovery procedures. -/
theorem indistinguishable_tail_matrices_of_short_menu {d n : ℕ} (hd : d<n^2)
    (c : Fin d → Fin n → ℂ) (T : ℝ) :
    ∃ f g : Fin n → CompactPulse, receiverWindowMatrix f (Ioi T)≠receiverWindowMatrix g (Ioi T) ∧
      ∀ k, reflectedWindowEnergy (mixedPulse univ (c k) f) (Ioi T)=
        reflectedWindowEnergy (mixedPulse univ (c k) g) (Ioi T) := by
  obtain ⟨H,hn,hH,hL⟩ := blind_hermitian_direction hd c
  let A := (H+1)ᴴ*(H+1)
  let B := (H-1)ᴴ*(H-1)
  have diff : A-B=(4:ℂ) • H := by
    have hs : (4:ℂ) • H=(H+H)+(H+H) := by ext i j; simp only [Matrix.smul_apply,smul_eq_mul,Matrix.add_apply]; ring
    rw [hs]
    dsimp only [A,B]
    rw [conjTranspose_add,conjTranspose_sub,hH.eq,conjTranspose_one]
    noncomm_ring
  have hne : A≠B := fun h => hn ((smul_eq_zero.mp (diff.symm.trans (sub_eq_zero.mpr h))).resolve_left (by norm_num))
  have equal : probeMatrix c A=probeMatrix c B := sub_eq_zero.mp (by
    rw [←map_sub,diff,map_smul,hL,smul_zero])
  obtain ⟨f,hf⟩ := (realizable_tail_matrix_iff_posSemidef T A).mpr (posSemidef_conjTranspose_mul_self _)
  obtain ⟨g,hg⟩ := (realizable_tail_matrix_iff_posSemidef T B).mpr (posSemidef_conjTranspose_mul_self _)
  refine ⟨f,g,by rwa [hf,hg],fun k => ?_⟩
  apply Complex.ofReal_injective
  rw [mixed_window_energy_gram,mixed_window_energy_gram]
  change probeMatrix c (receiverWindowMatrix f (Ioi T)) k=probeMatrix c (receiverWindowMatrix g (Ioi T)) k
  rw [hf,hg,equal]

/-- Sharp measurement count for arbitrary fixed complex mixtures. All
channels, time cutoffs and pulse families are included. -/
theorem least_number_of_complete_receiver_readings (n : ℕ) (T : ℝ) :
    IsLeast {d : ℕ | ∃ c : Fin d → Fin n → ℂ, ∀ f g : Fin n → CompactPulse,
      (∀ k, reflectedWindowEnergy (mixedPulse univ (c k) f) (Ioi T)=
        reflectedWindowEnergy (mixedPulse univ (c k) g) (Ioi T)) →
      receiverWindowMatrix f (Ioi T)=receiverWindowMatrix g (Ioi T)} (n^2) := by
  constructor
  · refine ⟨fun k i => (receiverSpiralStep^i.val)^k.val,fun f g h => ?_⟩
    have whole := (consecutive_spiral_readings_iff_gram f g (Ioi T) (Ioi T) 0).mp (fun j hj => by
      simpa only [Nat.zero_add,spiralMixedPulse] using h ⟨j,hj⟩)
    exact Matrix.ext whole
  · rintro d ⟨c,h⟩
    by_contra! hd
    obtain ⟨f,g,hne,he⟩ := indistinguishable_tail_matrices_of_short_menu hd c T
    exact hne (h f g he)

end GaloisForLFunctions.BlackHoleRingdown
