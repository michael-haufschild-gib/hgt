import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetThetaDomain

/-!
# Balanced cancellation of the full literal Fourier-jet cubic

The Gram is the sum of the two actual physical jet-output Gram matrices. Every
prime/Fourier cross entry is retained. Actual Fourier-pair independence proves its
positive definiteness, and physical Fourier on both outputs proves swap commutation.

At balanced theta visibility and contrast the constant-prime polarization commutes
with this entire Gram, so its complete modular cubic vanishes. Each prime has a
positive balancing parameter, yet its cubic displacement remains unbounded on that
same literal depth core. No common parameter balances two different primes.

The constant-theta helper is specialized to literal single-prime packets below;
it is not the varying-prime theta action on a mixed packet.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexOrder
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

def burnolJetOutputPairing (x y : BurnolJetAmbient) : ℂ :=
  ⟪x.2.1,y.2.1⟫_ℂ+⟪x.2.2,y.2.2⟫_ℂ

theorem burnolJetOutputPairing_swap (x y : BurnolJetAmbient) :
    burnolJetOutputPairing (burnolJetSwap x) (burnolJetSwap y) = burnolJetOutputPairing x y := by
  change ⟪fourierUnitary x.2.1,fourierUnitary y.2.1⟫_ℂ+
    ⟪fourierUnitary x.2.2,fourierUnitary y.2.2⟫_ℂ = _
  rw [fourierUnitary.inner_map_map,fourierUnitary.inner_map_map]
  unfold burnolJetOutputPairing
  abel

def primeBurnolJetGraphColumn {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    Fin N ⊕ Fin N → BurnolJetAmbient :=
  Sum.elim (fun i => burnolJetGraphVector (primeBurnolSquareColumn (pe i)) 0)
    (fun i => burnolJetGraphVector 0 (primeBurnolSquareColumn (pe i)))

theorem primeBurnolJetGraphColumn_swap {N : ℕ} (pe : Fin N → Nat.Primes × ℕ)
    (i : Fin N ⊕ Fin N) :
    primeBurnolJetGraphColumn pe (Sum.swap i) = burnolJetSwap (primeBurnolJetGraphColumn pe i) := by
  cases i with
  | inl i => exact (burnolJetSwap_source _ _
      (primeBurnolEvenFeatureLp_mem_evenSubspace (pe i)) evenSubspace.zero_mem).symm
  | inr i => exact (burnolJetSwap_source _ _
      evenSubspace.zero_mem (primeBurnolEvenFeatureLp_mem_evenSubspace (pe i))).symm

def primeBurnolFourierJetGram {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  fun i j => burnolJetOutputPairing (primeBurnolJetGraphColumn pe i) (primeBurnolJetGraphColumn pe j)

private theorem graph_output_first {N : ℕ} (pe : Fin N → Nat.Primes × ℕ)
    (i : Fin N ⊕ Fin N) : (primeBurnolJetGraphColumn pe i).2.1 = primeBurnolFourierPair pe i := by
  cases i with
  | inl i =>
    change (primeBurnolEvenFeatureLp (pe i))+fourierUnitary 0 = primeBurnolEvenFeatureLp (pe i)
    rw [map_zero,add_zero]
  | inr i =>
    change 0+fourierUnitary (primeBurnolEvenFeatureLp (pe i)) =
      fourierUnitary (primeBurnolEvenFeatureLp (pe i))
    rw [zero_add]

theorem primeBurnolFourierJetGram_posDef {N : ℕ} (pe : Fin N ↪ Nat.Primes × ℕ) :
    (primeBurnolFourierJetGram pe).PosDef := by
  have he : primeBurnolFourierJetGram pe = Matrix.gram ℂ (primeBurnolFourierPair pe)+
      Matrix.gram ℂ (fun i => (primeBurnolJetGraphColumn pe i).2.2) := by
    apply Matrix.ext
    intro i j
    change burnolJetOutputPairing (primeBurnolJetGraphColumn pe i) (primeBurnolJetGraphColumn pe j) =
      ⟪primeBurnolFourierPair pe i,primeBurnolFourierPair pe j⟫_ℂ+
      ⟪(primeBurnolJetGraphColumn pe i).2.2,(primeBurnolJetGraphColumn pe j).2.2⟫_ℂ
    unfold burnolJetOutputPairing
    rw [graph_output_first,graph_output_first]
  rw [he]
  exact (Matrix.posDef_gram_of_linearIndependent
    (primeBurnolFourierPair_linearIndependent pe)).add_posSemidef
      (Matrix.posSemidef_gram ℂ (fun i => (primeBurnolJetGraphColumn pe i).2.2))

def primeBurnolFourierJetGramUnit {N : ℕ} (pe : Fin N ↪ Nat.Primes × ℕ) :
    (Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ)ˣ :=
  (primeBurnolFourierJetGram_posDef pe).isUnit.unit

theorem coe_primeBurnolFourierJetGramUnit {N : ℕ} (pe : Fin N ↪ Nat.Primes × ℕ) :
    (primeBurnolFourierJetGramUnit pe : Matrix _ _ ℂ) = primeBurnolFourierJetGram pe :=
  IsUnit.unit_spec _

def burnolJetSwapMatrix (N : ℕ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  fun i j => if i=Sum.swap j then 1 else 0

private theorem swapMatrix_mul {N : ℕ} (A : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ)
    (i j : Fin N ⊕ Fin N) : (burnolJetSwapMatrix N*A) i j = A (Sum.swap i) j := by
  have he (k : Fin N ⊕ Fin N) : (i=Sum.swap k) ↔ (k=Sum.swap i) := by
    constructor <;> intro h <;> simpa using congrArg Sum.swap h.symm
  simp only [Matrix.mul_apply,burnolJetSwapMatrix,he,ite_mul,one_mul,zero_mul]
  simp

private theorem mul_swapMatrix {N : ℕ} (A : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ)
    (i j : Fin N ⊕ Fin N) : (A*burnolJetSwapMatrix N) i j = A i (Sum.swap j) := by
  simp [Matrix.mul_apply,burnolJetSwapMatrix,mul_ite]

theorem primeBurnolFourierJetGram_commutes_swap {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    primeBurnolFourierJetGram pe*burnolJetSwapMatrix N =
      burnolJetSwapMatrix N*primeBurnolFourierJetGram pe := by
  ext i j
  rw [mul_swapMatrix,swapMatrix_mul]
  have h := burnolJetOutputPairing_swap (primeBurnolJetGraphColumn pe i)
    (primeBurnolJetGraphColumn pe (Sum.swap j))
  rw [← primeBurnolJetGraphColumn_swap,← primeBurnolJetGraphColumn_swap,Sum.swap_swap] at h
  exact h.symm


def burnolJetNeutralMatrix (N : ℕ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks 1 0 0 0

def burnolJetThetaMatrix (N : ℕ) (p : Nat.Primes) (a : ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks ((primeBurnolThetaVisibility a p : ℂ)^2 • 1)
    (((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)) • 1)
    (((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)) • 1)
    ((primeBurnolThetaContrast a p : ℂ)^2 • 1)

def burnolJetRotationMatrix (N : ℕ) (p : Nat.Primes) (a : ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks ((primeBurnolThetaVisibility a p : ℂ) • 1)
    (-(primeBurnolThetaContrast a p : ℂ) • 1)
    ((primeBurnolThetaContrast a p : ℂ) • 1)
    ((primeBurnolThetaVisibility a p : ℂ) • 1)

def primeBurnolJetSourceColumn {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    Fin N ⊕ Fin N → burnolSquarePosition.domain × burnolSquarePosition.domain :=
  Sum.elim (fun i => (primeBurnolSquareColumn (pe i),0))
    (fun i => (0,primeBurnolSquareColumn (pe i)))

theorem burnolJetThetaMatrix_source_action {N : ℕ} (pe : Fin N → Nat.Primes × ℕ)
    (p : Nat.Primes) (a : ℝ) (i : Fin N ⊕ Fin N) :
    burnolJetGraphLinear (burnolJetPrimeThetaSource p a (primeBurnolJetSourceColumn pe i)) =
      ∑ j, (burnolJetThetaMatrix N p a) j i • primeBurnolJetGraphColumn pe j := by
  have h : 1-(primeBurnolThetaVisibility a p : ℂ)^2=(primeBurnolThetaContrast a p : ℂ)^2 := by
    have hh : (primeBurnolThetaVisibility a p : ℂ)^2+(primeBurnolThetaContrast a p : ℂ)^2=1 := by
      exact_mod_cast primeBurnolThetaVisibility_sq_add_contrast_sq a p
    linear_combination -hh
  cases i with
  | inl i =>
    simp only [Fintype.sum_sum_type,burnolJetThetaMatrix,Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₂₁,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,
      mul_ite,mul_one,mul_zero,ite_smul,zero_smul]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    change burnolJetGraphLinear _ =
      (primeBurnolThetaVisibility a p : ℂ)^2 • burnolJetGraphLinear (primeBurnolSquareColumn (pe i),0)+
      ((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)) •
        burnolJetGraphLinear (0,primeBurnolSquareColumn (pe i))
    rw [← map_smul,← map_smul,← map_add]
    congr 1
    apply Prod.ext <;>
      simp only [burnolJetPrimeThetaSource,burnolJetThetaSource,primeBurnolJetSourceColumn,
        Sum.elim_inl,LinearMap.coe_mk,AddHom.coe_mk,Prod.fst_add,Prod.snd_add,
        Prod.smul_fst,Prod.smul_snd,smul_zero,add_zero,zero_add]
  | inr i =>
    simp only [Fintype.sum_sum_type,burnolJetThetaMatrix,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₂,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,
      mul_ite,mul_one,mul_zero,ite_smul,zero_smul]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    change burnolJetGraphLinear _ =
      ((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)) •
        burnolJetGraphLinear (primeBurnolSquareColumn (pe i),0)+
      (primeBurnolThetaContrast a p : ℂ)^2 • burnolJetGraphLinear (0,primeBurnolSquareColumn (pe i))
    rw [← map_smul,← map_smul,← map_add]
    congr 1
    apply Prod.ext <;>
      simp only [burnolJetPrimeThetaSource,burnolJetThetaSource,primeBurnolJetSourceColumn,
        Sum.elim_inr,LinearMap.coe_mk,AddHom.coe_mk,Prod.fst_add,Prod.snd_add,
        Prod.smul_fst,Prod.smul_snd,smul_zero,add_zero,zero_add,h]

theorem burnolJetThetaMatrix_frame (N : ℕ) (p : Nat.Primes) (a : ℝ) :
    burnolJetThetaMatrix N p a =
      burnolJetRotationMatrix N p a*burnolJetNeutralMatrix N*burnolJetRotationMatrix N p (-a) := by
  unfold burnolJetThetaMatrix burnolJetRotationMatrix burnolJetNeutralMatrix
  rw [primeBurnolThetaVisibility_neg,primeBurnolThetaContrast_neg]
  simp only [Complex.ofReal_neg,neg_neg,Matrix.fromBlocks_multiply,Matrix.mul_smul,
    Matrix.mul_one,Matrix.mul_zero,smul_zero,smul_smul,add_zero]
  congr 1 <;> congr 1 <;> ring

theorem burnolJetRotationMatrix_inverse (N : ℕ) (p : Nat.Primes) (a : ℝ) :
    burnolJetRotationMatrix N p a*burnolJetRotationMatrix N p (-a)=1 := by
  have h : (primeBurnolThetaVisibility a p : ℂ)^2+(primeBurnolThetaContrast a p : ℂ)^2=1 := by
    exact_mod_cast primeBurnolThetaVisibility_sq_add_contrast_sq a p
  have hd : (primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaVisibility a p : ℂ)+
      (primeBurnolThetaContrast a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)=1 := by
    simpa only [pow_two] using h
  unfold burnolJetRotationMatrix
  rw [primeBurnolThetaVisibility_neg,primeBurnolThetaContrast_neg]
  simp only [Complex.ofReal_neg,neg_neg,Matrix.fromBlocks_multiply,Matrix.mul_smul,
    Matrix.smul_mul,Matrix.one_mul,smul_smul,← add_smul]
  rw [show -(primeBurnolThetaContrast a p : ℂ)*(-(primeBurnolThetaContrast a p : ℂ)) =
      (primeBurnolThetaContrast a p : ℂ)*(primeBurnolThetaContrast a p : ℂ) by ring,hd,
    show (primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)+
      -(primeBurnolThetaContrast a p : ℂ)*(primeBurnolThetaVisibility a p : ℂ)=0 by ring,
    show (primeBurnolThetaContrast a p : ℂ)*(primeBurnolThetaVisibility a p : ℂ)+
      (primeBurnolThetaVisibility a p : ℂ)*(-(primeBurnolThetaContrast a p : ℂ))=0 by ring,
    add_comm ((primeBurnolThetaContrast a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)),hd]
  simp only [one_smul,zero_smul,Matrix.fromBlocks_one]

theorem burnolJetThetaMatrix_balanced (N : ℕ) (p : Nat.Primes) (a : ℝ) :
    primeBurnolThetaVisibility a p^2=primeBurnolThetaContrast a p^2 →
      burnolJetThetaMatrix N p a =
        (primeBurnolThetaVisibility a p : ℂ)^2 • 1+
        ((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)) •
          burnolJetSwapMatrix N := by
  intro hb
  have h : (primeBurnolThetaVisibility a p : ℂ)^2=(primeBurnolThetaContrast a p : ℂ)^2 :=
    by exact_mod_cast hb
  ext i j
  cases i <;> cases j <;>
    simp [burnolJetThetaMatrix,burnolJetSwapMatrix,Matrix.fromBlocks,Matrix.one_apply,h]

def primeBurnolFourierJetConstantThetaCubic {N : ℕ} (pe : Fin N ↪ Nat.Primes × ℕ)
    (p : Nat.Primes) (a : ℝ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  cubicProjectionAssociatorAlgebra
    (sourceModularAutomorphism (primeBurnolFourierJetGramUnit pe) (burnolJetThetaMatrix N p a))
    (burnolJetThetaMatrix N p a) (burnolJetNeutralMatrix N)

theorem primeBurnolFourierJetConstantThetaCubic_balanced {N : ℕ} (pe : Fin N ↪ Nat.Primes × ℕ)
    (p : Nat.Primes) (a : ℝ) :
    primeBurnolThetaVisibility a p^2=primeBurnolThetaContrast a p^2 →
      primeBurnolFourierJetConstantThetaCubic pe p a=0 := by
  intro hb
  have hc : (primeBurnolFourierJetGramUnit pe : Matrix _ _ ℂ)*burnolJetThetaMatrix N p a =
      burnolJetThetaMatrix N p a*(primeBurnolFourierJetGramUnit pe : Matrix _ _ ℂ) := by
    rw [coe_primeBurnolFourierJetGramUnit,burnolJetThetaMatrix_balanced N p a hb]
    simp only [mul_add,add_mul,Matrix.mul_smul,Matrix.smul_mul,mul_one,one_mul,
      primeBurnolFourierJetGram_commutes_swap]
  have hR : sourceModularAutomorphism (primeBurnolFourierJetGramUnit pe)
      (burnolJetThetaMatrix N p a) = burnolJetThetaMatrix N p a := by
    change (↑((primeBurnolFourierJetGramUnit pe)⁻¹) : Matrix _ _ ℂ)*
      burnolJetThetaMatrix N p a*(primeBurnolFourierJetGramUnit pe : Matrix _ _ ℂ) = _
    rw [mul_assoc,← hc,← mul_assoc,Units.inv_mul,one_mul]
  unfold primeBurnolFourierJetConstantThetaCubic
  rw [hR]
  simp only [cubicProjectionAssociatorAlgebra,sub_self,zero_pow (by decide : 3 ≠ 0),sub_zero]


def primeBurnolSelectedDepthPacket (p : Nat.Primes) {N : ℕ} (d : Fin N ↪ ℕ) :
    Fin N ↪ Nat.Primes × ℕ where
  toFun i := (p,d i)
  inj' _ _ h := d.injective (congrArg Prod.snd h)

theorem primeBurnolTheta_balanced_exists (p : Nat.Primes) :
    ∃ a : ℝ, 0<a ∧ primeBurnolThetaVisibility a p^2=primeBurnolThetaContrast a p^2 := by
  let c := Real.sqrt (1/2 : ℝ)
  have hc : 0<c := Real.sqrt_pos.mpr (by norm_num)
  have hs : c^2=1/2 := Real.sq_sqrt (by norm_num)
  have hc1 : c<1 := by nlinarith
  have him : c ∈ Real.tanh '' Set.Ioi 0 := by
    rw [_root_.HTGeometry.tanh_image_Ioi_zero]
    exact ⟨hc,hc1⟩
  obtain ⟨t,ht,htc⟩ := him
  have hlog : 0<Real.log (p : ℝ) := (primeBurnolLogRate p).property
  refine ⟨2*t/Real.log (p : ℝ),div_pos (mul_pos (by norm_num) ht) hlog,?_⟩
  have hr : primeBurnolThetaRapidity (2*t/Real.log (p : ℝ)) p=t := by
    unfold primeBurnolThetaRapidity
    field_simp
  have hcon : primeBurnolThetaContrast (2*t/Real.log (p : ℝ)) p=c := by
    rw [primeBurnolThetaContrast,hr]
    exact htc
  have hpy := primeBurnolThetaVisibility_sq_add_contrast_sq (2*t/Real.log (p : ℝ)) p
  rw [hcon] at hpy ⊢
  linarith

theorem burnolJetPrimeTheta_displacement_cube_no_prime_graph_bound
    (p : Nat.Primes) (a : ℝ) : a≠0 →
    ¬ (∃ C : ℝ, 0 ≤ C ∧ ∀ f g : burnolSquarePosition.domain,
      ((f : SoninL2),burnolSquarePosition f) ∈ primeBurnolSquareGraphCore p →
      ((g : SoninL2),burnolSquarePosition g) ∈ primeBurnolSquareGraphCore p →
      ‖burnolJetGraphLinear (((burnolJetPrimeThetaSource p a-burnolJetNeutralSource)^3) (f,g))‖ ≤
        C*‖burnolJetGraphVector f g‖) := by
  intro ha
  rintro ⟨C,hC,hbound⟩
  let A : ℂ := -2*(primeBurnolThetaContrast a p : ℂ)^4
  let B : ℂ := (primeBurnolThetaContrast a p : ℂ)^4
  let D : ℂ := (primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)^3
  have hc : (primeBurnolThetaContrast a p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr ((primeBurnolThetaContrast_eq_zero_iff p a).not.mpr ha)
  have hA : 0<‖A‖ := norm_pos_iff.mpr (mul_ne_zero (by norm_num) (pow_ne_zero _ hc))
  apply burnolJetNeutral_no_prime_graph_bound p
  refine ⟨(C+‖B‖+‖D‖)/‖A‖,div_nonneg (by positivity) hA.le,?_⟩
  intro f g hf hg
  have he {v : burnolSquarePosition.domain}
      (hv : ((v : SoninL2),burnolSquarePosition v) ∈ primeBurnolSquareGraphCore p) :
      (v : SoninL2) ∈ evenSubspace := by
    have hx := (primeBurnolSquareGraphCore p).le_topologicalClosure hv
    rw [primeBurnolSquareGraphCore_closure] at hx
    exact hx.2.1
  have hb : ‖A • burnolJetGraphVector f 0+B • burnolJetGraphVector f g+
      D • burnolJetSwap (burnolJetGraphVector f g)‖ ≤ C*‖burnolJetGraphVector f g‖ := by
    have hh := hbound f g hf hg
    rw [burnolJetPrimeTheta_displacement_cube_graph p a f g (he hf) (he hg)] at hh
    exact hh
  have hrecover : A • burnolJetGraphVector f 0 =
      (A • burnolJetGraphVector f 0+B • burnolJetGraphVector f g+
      D • burnolJetSwap (burnolJetGraphVector f g))-B • burnolJetGraphVector f g-
      D • burnolJetSwap (burnolJetGraphVector f g) := by abel
  have hh : ‖A‖*‖burnolJetGraphVector f 0‖ ≤
      (C+‖B‖+‖D‖)*‖burnolJetGraphVector f g‖ := by
    rw [← norm_smul,hrecover]
    have h1 := norm_sub_le
      (A • burnolJetGraphVector f 0+B • burnolJetGraphVector f g+
        D • burnolJetSwap (burnolJetGraphVector f g)-B • burnolJetGraphVector f g)
      (D • burnolJetSwap (burnolJetGraphVector f g))
    have h2 := norm_sub_le
      (A • burnolJetGraphVector f 0+B • burnolJetGraphVector f g+
        D • burnolJetSwap (burnolJetGraphVector f g)) (B • burnolJetGraphVector f g)
    rw [norm_smul,burnolJetSwap.norm_map] at h1
    rw [norm_smul] at h2
    nlinarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hA).mpr
  simpa only [mul_comm ‖A‖ ‖burnolJetGraphVector f 0‖] using hh

/-- The actual full cubic of a literal single-prime depth packet. -/
def primeBurnolFourierJetSinglePrimeCubic (p : Nat.Primes) {N : ℕ}
    (d : Fin N ↪ ℕ) (a : ℝ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  primeBurnolFourierJetConstantThetaCubic (primeBurnolSelectedDepthPacket p d) p a

/-- Full finite cubic cancellation can coexist with unbounded displacement on the same prime core. -/
theorem primeBurnolFourierJet_balanced_cancellation_exists (p : Nat.Primes) :
    ∃ a : ℝ, 0<a ∧
      (∀ (N : ℕ) (d : Fin N ↪ ℕ),
        primeBurnolFourierJetSinglePrimeCubic p d a=0) ∧
      ¬ (∃ C : ℝ, 0 ≤ C ∧ ∀ f g : burnolSquarePosition.domain,
        ((f : SoninL2),burnolSquarePosition f) ∈ primeBurnolSquareGraphCore p →
        ((g : SoninL2),burnolSquarePosition g) ∈ primeBurnolSquareGraphCore p →
        ‖burnolJetGraphLinear (((burnolJetPrimeThetaSource p a-burnolJetNeutralSource)^3) (f,g))‖ ≤
          C*‖burnolJetGraphVector f g‖) := by
  obtain ⟨a,ha,hbalance⟩ := primeBurnolTheta_balanced_exists p
  refine ⟨a,ha,fun N d => primeBurnolFourierJetConstantThetaCubic_balanced _ p a hbalance,?_⟩
  exact burnolJetPrimeTheta_displacement_cube_no_prime_graph_bound p a ha.ne'


theorem primeBurnolTheta_balanced_prime_unique (a : ℝ) :
    Set.Subsingleton {p : Nat.Primes |
      primeBurnolThetaVisibility a p^2=primeBurnolThetaContrast a p^2} := by
  intro p hp q hq
  change primeBurnolThetaVisibility a p^2=primeBurnolThetaContrast a p^2 at hp
  change primeBurnolThetaVisibility a q^2=primeBurnolThetaContrast a q^2 at hq
  have ha : a≠0 := by
    intro h
    subst a
    norm_num [primeBurnolThetaVisibility_zero,primeBurnolThetaContrast_zero] at hp
  have hp' := primeBurnolThetaVisibility_sq_add_contrast_sq a p
  have hq' := primeBurnolThetaVisibility_sq_add_contrast_sq a q
  have hs : primeBurnolThetaContrast a p^2=primeBurnolThetaContrast a q^2 := by
    change primeBurnolThetaVisibility a p^2=primeBurnolThetaContrast a p^2 at hp
    change primeBurnolThetaVisibility a q^2=primeBurnolThetaContrast a q^2 at hq
    linarith
  have hsign (r : Nat.Primes) :
      (0≤a → 0≤primeBurnolThetaContrast a r) ∧
      (a≤0 → primeBurnolThetaContrast a r≤0) := by
    constructor
    · intro ha
      have hh : 0≤primeBurnolThetaRapidity a r :=
        div_nonneg (mul_nonneg ha (primeBurnolLogRate r).property.le) (by norm_num)
      have h := _root_.HTGeometry.tanh_strictMono.monotone hh
      simpa only [Real.tanh_zero,primeBurnolThetaContrast] using h
    · intro ha
      have hh : primeBurnolThetaRapidity a r≤0 :=
        div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg ha (primeBurnolLogRate r).property.le) (by norm_num)
      have h := _root_.HTGeometry.tanh_strictMono.monotone hh
      simpa only [Real.tanh_zero,primeBurnolThetaContrast] using h
  have he : primeBurnolThetaContrast a p=primeBurnolThetaContrast a q := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
    · exact h
    · rcases le_total 0 a with ha | ha
      · have h1 := (hsign p).1 ha
        have h2 := (hsign q).1 ha
        linarith
      · have h1 := (hsign p).2 ha
        have h2 := (hsign q).2 ha
        linarith
  have hr := _root_.HTGeometry.tanh_strictMono.injective he
  change a*Real.log (p : ℝ)/2=a*Real.log (q : ℝ)/2 at hr
  have hprod : a*(Real.log (p : ℝ)-Real.log (q : ℝ))=0 := by linarith
  have hlog := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left ha)
  have hp0 : 0<(p : ℝ) := by exact_mod_cast p.property.pos
  have hq0 : 0<(q : ℝ) := by exact_mod_cast q.property.pos
  have hpq := Real.log_injOn_pos hp0 hq0 hlog
  apply Subtype.ext
  exact_mod_cast hpq

end RHTower
