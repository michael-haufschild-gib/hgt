import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.OnePhaseSweepOfTheReflectedPulseGram
import GaloisForLFunctions.BlackHoleRingdown.PassiveTwinEchoAndFiniteTimeDistinction
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.LinearAlgebra.Lagrange

/-!
# Recovery of every receiver cross-energy from one geometric sequence

At setting k, channel j has amplitude ((2+i)/3)^(jk). Distinct ordered
pairs give different complex moment nodes: their absolute values identify
the sum of the indices, and a Gaussian prime separates the phase powers.
Lagrange interpolation recovers the complete receiver Gram matrix from any
n² consecutive scalar energies, with one fixed multiplier for all n.
-/

noncomputable section
open Complex Finset Polynomial Set MeasureTheory
open scoped ComplexConjugate
namespace GaloisForLFunctions.BlackHoleRingdown

/-- Rational complex amplitude step inside the unit disk. -/
def receiverSpiralStep : ℂ := (2+I)/3

private theorem step_normSq : normSq receiverSpiralStep=5/9 := by
  rw [receiverSpiralStep,normSq_div,normSq_ofNat,normSq_apply]
  norm_num [Complex.add_re,Complex.add_im]

private theorem step_ne_zero : receiverSpiralStep ≠ 0 := by
  intro hz
  have h := step_normSq
  rw [hz,map_zero] at h
  norm_num at h

/-- The Gaussian reduction i ↦ 2 modulo 5 kills 2−i and preserves 2+i.
Consequently conjugate powers never coincide at a positive exponent. -/
private theorem unequal_conjugate_powers {k : ℕ} (hk : 0<k) :
    receiverSpiralStep^k ≠ (conj receiverSpiralStep)^k := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let a : GaussianInt := ⟨2,1⟩
  let b : GaussianInt := ⟨2,-1⟩
  let φ : GaussianInt →+* ZMod 5 := Zsqrtd.lift ⟨(2:ZMod 5),by decide⟩
  have ha : GaussianInt.toComplex a=2+I := by
    change ((⟨2,1⟩ : GaussianInt):ℂ)=_
    norm_num [GaussianInt.toComplex_def']
  have hb : GaussianInt.toComplex b=2-I := by
    change ((⟨2,-1⟩ : GaussianInt):ℂ)=_
    norm_num [GaussianInt.toComplex_def',sub_eq_add_neg]
  have ha' : φ a=4 := by decide
  have hb' : φ b=0 := by decide
  intro h
  have hh : (2+I)^k=(2-I)^k := by
    change ((2+I)/3)^k=(conj ((2+I)/3))^k at h
    simp only [map_div₀,map_add,map_ofNat,Complex.conj_I,←sub_eq_add_neg,div_pow] at h
    exact (div_left_inj' (pow_ne_zero k (by norm_num : (3:ℂ)≠0))).mp h
  have hab : a^k=b^k := GaussianInt.toComplex_injective (by simpa only [map_pow,ha,hb] using hh)
  have hφ := congrArg φ hab
  rw [map_pow,map_pow,ha',hb',zero_pow hk.ne'] at hφ
  exact (pow_ne_zero k (by decide : (4:ZMod 5)≠0)) hφ

def receiverSpiralNode (ij : ℕ × ℕ) : ℂ :=
  receiverSpiralStep^ij.1*(conj receiverSpiralStep)^ij.2

private theorem node_ne_zero (q : ℕ × ℕ) : receiverSpiralNode q≠0 :=
  mul_ne_zero (pow_ne_zero _ step_ne_zero)
    (pow_ne_zero _ ((map_ne_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).mpr step_ne_zero))

/-- Pair labels remain separated simultaneously in every channel dimension. -/
theorem receiver_spiral_nodes_injective : Function.Injective receiverSpiralNode := by
  rintro ⟨a,b⟩ ⟨c,d⟩ he
  change receiverSpiralStep^a*(conj receiverSpiralStep)^b=
    receiverSpiralStep^c*(conj receiverSpiralStep)^d at he
  have hn := congrArg normSq he
  simp only [map_mul,map_pow,normSq_conj,step_normSq,←pow_add] at hn
  have hs : a+b=c+d := (pow_right_inj₀ (by norm_num : 0<(5/9:ℝ)) (by norm_num)).mp hn
  have impossible {a b c d : ℕ} (hs : a+b=c+d) (hac : a<c)
      (eq : receiverSpiralStep^a*(conj receiverSpiralStep)^b=
        receiverSpiralStep^c*(conj receiverSpiralStep)^d) : False := by
    let k := c-a
    have hk : 0<k := Nat.sub_pos_of_lt hac
    have h₁ : a+k=c := by dsimp only [k]; omega
    have h₂ : d+k=b := by dsimp only [k]; omega
    have h :
        receiverSpiralNode (a,d)*(conj receiverSpiralStep)^k=receiverSpiralNode (a,d)*receiverSpiralStep^k := by
      calc _ = receiverSpiralStep^a*((conj receiverSpiralStep)^d*(conj receiverSpiralStep)^k) := by
                  unfold receiverSpiralNode; ring
           _ = receiverSpiralStep^c*(conj receiverSpiralStep)^d := by rwa [←pow_add,h₂]
           _ = _ := by rw [←h₁,pow_add]; unfold receiverSpiralNode; ring
    exact unequal_conjugate_powers hk (mul_left_cancel₀ (node_ne_zero _) h).symm
  have hac : a=c := le_antisymm (le_of_not_gt (fun h => impossible hs.symm h he.symm))
    (le_of_not_gt (fun h => impossible hs h he))
  exact Prod.ext hac (by omega)

private def spiralNode {n : ℕ} (q : Fin n × Fin n) : ℂ :=
  receiverSpiralNode (q.1.val,q.2.val)

private theorem spiralNode_injective (n : ℕ) : Function.Injective (@spiralNode n) := by
  intro p q h
  have he := receiver_spiral_nodes_injective h
  exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

/-- One scalar energy setting mixes every input pulse with an explicitly
known Gaussian rational. -/
def spiralMixedPulse {n : ℕ} (f : Fin n → CompactPulse) (k : ℕ) :=
  mixedPulse univ (fun i : Fin n => (receiverSpiralStep^i.val)^k) f

private theorem spiral_readout {n : ℕ} (f : Fin n → CompactPulse) (W : Set ℝ) (k : ℕ) :
    (reflectedWindowEnergy (spiralMixedPulse f k) W:ℂ)=
      ∑ q : Fin n × Fin n, reflectedWindowGram (f q.1) (f q.2) W*(spiralNode q)^k := by
  simp only [spiralMixedPulse,mixed_window_energy_gram,Fintype.sum_prod_type,spiralNode,receiverSpiralNode,
    mul_pow,map_pow]

/-- Polynomial giving the dual weights on successive measured energies. -/
def spiralRecoveryPolynomial {n : ℕ} (q : Fin n × Fin n) : ℂ[X] :=
  Lagrange.basis univ spiralNode q

/-- Every entry, including diagonal energy, is read by the same n² settings
in any prescribed consecutive block. The reconstruction weights depend
only on the channel labels and the starting index. -/
theorem recover_full_receiver_gram_from_spiral {n : ℕ} (f : Fin n → CompactPulse) (W : Set ℝ)
    (K : ℕ) (q : Fin n × Fin n) :
    (∑ j ∈ range (n^2), (spiralRecoveryPolynomial q).coeff j*
        (reflectedWindowEnergy (spiralMixedPulse f (K+j)) W:ℂ))/(spiralNode q)^K=
      reflectedWindowGram (f q.1) (f q.2) W := by
  let L := spiralRecoveryPolynomial q
  let G := fun p : Fin n × Fin n => reflectedWindowGram (f p.1) (f p.2) W
  have hd : L.natDegree<n^2 := by
    have hn : 0<n := (Nat.zero_le q.1.val).trans_lt q.1.isLt
    have he := Lagrange.natDegree_basis (spiralNode_injective n).injOn (mem_univ q)
    simp only [card_univ,Fintype.card_prod,Fintype.card_fin,←sq] at he
    exact he.trans_lt (Nat.sub_one_lt (pow_ne_zero _ hn.ne'))
  have point (p : Fin n × Fin n) : L.eval (spiralNode p) = if p=q then 1 else 0 := by
    rcases eq_or_ne p q with rfl | h
    · exact (Lagrange.eval_basis_self (spiralNode_injective n).injOn (mem_univ _)).trans (if_pos rfl).symm
    · exact (Lagrange.eval_basis_of_ne h.symm (mem_univ _)).trans (if_neg h).symm
  have eq (p : Fin n × Fin n) :
      (∑ j ∈ range (n^2), L.coeff j*(G p*(spiralNode p)^(K+j))) =
        G p*(spiralNode p)^K*L.eval (spiralNode p) := by
    rw [Polynomial.eval_eq_sum_range' hd,Finset.mul_sum]
    exact sum_congr rfl fun j _ => by rw [pow_add]; ring
  apply (div_eq_iff (pow_ne_zero _ (node_ne_zero _))).mpr
  simp_rw [spiral_readout,Finset.mul_sum]
  rw [sum_comm]
  change (∑ p : Fin n × Fin n, ∑ j ∈ range (n^2), L.coeff j*(G p*(spiralNode p)^(K+j)))=_
  simp only [eq,point,mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,if_true,G]

/-- Two experiments agree on a full window Gram matrix exactly when
their n² consecutive scalar readings agree. -/
theorem consecutive_spiral_readings_iff_gram {n : ℕ} (f g : Fin n → CompactPulse)
    (W V : Set ℝ) (K : ℕ) :
    (∀ j < n^2, reflectedWindowEnergy (spiralMixedPulse f (K+j)) W=
      reflectedWindowEnergy (spiralMixedPulse g (K+j)) V) ↔
    ∀ i j, reflectedWindowGram (f i) (f j) W=reflectedWindowGram (g i) (g j) V := by
  constructor
  · intro h i j
    rw [←recover_full_receiver_gram_from_spiral f W K (i,j),←recover_full_receiver_gram_from_spiral g V K (i,j)]
    exact congrArg (fun z : ℂ => z/(spiralNode (i,j))^K) (sum_congr rfl fun k hk =>
      congrArg (fun z : ℝ => (spiralRecoveryPolynomial (i,j)).coeff k*(z:ℂ)) (h k (mem_range.mp hk)))
  · intro h k _
    apply Complex.ofReal_injective
    simp only [spiral_readout,h]

/-- Errors in a late block grow by the reciprocal modulus of the node
at each omitted setting. The remaining factor is independent of the
starting index and the receiver window. -/
theorem spiral_pair_error_bound {n : ℕ} (f g : Fin n → CompactPulse) (W V : Set ℝ)
    (K : ℕ) (q : Fin n × Fin n) {ε : ℝ}
    (h : ∀ j<n^2, |reflectedWindowEnergy (spiralMixedPulse f (K+j)) W-
      reflectedWindowEnergy (spiralMixedPulse g (K+j)) V|≤ε) :
    ‖reflectedWindowGram (f q.1) (f q.2) W-reflectedWindowGram (g q.1) (g q.2) V‖ ≤
      ((∑ j ∈ range (n^2), ‖(spiralRecoveryPolynomial q).coeff j‖)*ε)/‖spiralNode q‖^K := by
  rw [←recover_full_receiver_gram_from_spiral f W K q,←recover_full_receiver_gram_from_spiral g V K q,
    ←sub_div,norm_div,norm_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [←sum_sub_distrib,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro j hj
  rw [←mul_sub,norm_mul,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (h j (mem_range.mp hj)) (norm_nonneg _)

/-- A physical family in which only channel i carries an incident pulse. -/
def isolatedSpiralChannel {n : ℕ} (i : Fin n) (h : CompactPulse) (j : Fin n) :=
  if j=i then h else CompactPulse.zero

theorem isolated_spiral_readout {n : ℕ} (i : Fin n) (h : CompactPulse) (W : Set ℝ) (k : ℕ) :
    reflectedWindowEnergy (spiralMixedPulse (isolatedSpiralChannel i h) k) W=
      (5/9:ℝ)^(i.val*k)*reflectedWindowEnergy h W := by
  have ht (t : ℝ) : pulseReflected (spiralMixedPulse (isolatedSpiralChannel i h) k) t=
      (receiverSpiralStep^i.val)^k*pulseReflected h t := by
    rw [spiralMixedPulse,pulseReflected_mixedPulse,sum_eq_single i]
    · simp only [isolatedSpiralChannel,if_pos rfl]
    · intro j _ hji
      rw [isolatedSpiralChannel,if_neg hji,pulseReflected_zero,mul_zero]
    · intro hi
      exact (hi (mem_univ _)).elim
  have hgain : ‖(receiverSpiralStep^i.val)^k‖^2=(5/9:ℝ)^(i.val*k) := by
    rw [←pow_mul,norm_pow,←pow_mul,Nat.mul_comm (i.val*k) 2,pow_mul,Complex.sq_norm,step_normSq]
  simp only [reflectedWindowEnergy,ht,norm_mul,mul_pow,hgain,integral_const_mul]

/-- On a single nonzero channel, the first reading in the block is the
largest. This gives the full exponential loss even for genuine nonnegative
scalar pulse energies. -/
theorem peak_isolated_spiral_readout {n : ℕ} (i : Fin n) (h : CompactPulse) (W : Set ℝ) (K : ℕ) :
    IsGreatest ((fun j : ℕ => reflectedWindowEnergy (spiralMixedPulse (isolatedSpiralChannel i h) (K+j)) W)
      '' {j | j<n^2}) ((5/9:ℝ)^(i.val*K)*reflectedWindowEnergy h W) := by
  have hn : 0<n := (Nat.zero_le i.val).trans_lt i.isLt
  constructor
  · exact ⟨0,pow_pos hn _,by rw [Nat.add_zero,isolated_spiral_readout]⟩
  · rintro _ ⟨j,_,rfl⟩
    rw [isolated_spiral_readout,Nat.mul_add,pow_add]
    apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun _ => sq_nonneg _)
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))

/-- Uniform error coefficients for recovery of the ith channel's own
energy from the block beginning at setting K. -/
def spiralDiagonalConstants {n : ℕ} (i : Fin n) (K : ℕ) : Set ℝ :=
  {L | ∀ (f g : Fin n → CompactPulse) (W V : Set ℝ) (ε : ℝ),
    (∀ j<n^2, |reflectedWindowEnergy (spiralMixedPulse f (K+j)) W-
      reflectedWindowEnergy (spiralMixedPulse g (K+j)) V|≤ε) →
    |reflectedWindowEnergy (f i) W-reflectedWindowEnergy (g i) V|≤L*ε}

/-- The diagonal noise cost grows exactly at the exponential rate
(9/5)^(iK). An isolated nonzero physical pulse gives the lower bound.
The Lagrange decoder gives the upper bound with a fixed factor. -/
theorem sharp_exponential_diagonal_cost {n : ℕ} (i : Fin n) :
    ∃ C : ℝ, ∀ K : ℕ, C/(5/9:ℝ)^(i.val*K)∈spiralDiagonalConstants i K ∧
      ∀ L∈spiralDiagonalConstants i K, 1/(5/9:ℝ)^(i.val*K)≤L := by
  let C := ∑ j ∈ range (n^2), ‖(spiralRecoveryPolynomial (i,i)).coeff j‖
  refine ⟨C,fun K => ⟨?_,?_⟩⟩
  · intro f g W V ε he
    have h := spiral_pair_error_bound f g W V K (i,i) he
    have hnode : ‖spiralNode (i,i)‖^K=(5/9:ℝ)^(i.val*K) := by
      simp only [spiralNode,receiverSpiralNode,←mul_pow,Complex.mul_conj,step_normSq,norm_pow,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by norm_num : 0<(5/9:ℝ)),←pow_mul]
    rw [reflectedWindowGram_self,reflectedWindowGram_self,←Complex.ofReal_sub,Complex.norm_real,
      Real.norm_eq_abs,hnode] at h
    change _≤C*ε/(5/9:ℝ)^(i.val*K) at h
    linarith only [h]
  · intro L hL
    let p := scaledBumpPulse 1 zero_lt_one
    have hp : ∃ t : ℝ, p t≠0 := by
      by_contra! hz
      have h := integral_norm_sq_scaledBumpPulse_pos (R:=1) zero_lt_one
      change 0<∫ t : ℝ, ‖p t‖^2 at h
      simp only [hz,norm_zero,zero_pow (by decide : 2≠0),integral_zero,lt_self_iff_false] at h
    let W := Ioi (0:ℝ)
    let E := reflectedWindowEnergy p W
    let A := (5/9:ℝ)^(i.val*K)
    have hE : 0<E := tailEnergy_pos p hp 0
    have hA : 0<A := by dsimp only [A]; positivity
    let f := isolatedSpiralChannel i p
    have hempty (r : CompactPulse) : reflectedWindowEnergy r ∅=0 := by simp [reflectedWindowEnergy]
    have hpeak := peak_isolated_spiral_readout i p W K
    have measured (j : ℕ) (hj : j<n^2) : |reflectedWindowEnergy (spiralMixedPulse f (K+j)) W-
        reflectedWindowEnergy (spiralMixedPulse f (K+j)) ∅|≤A*E := by
      rw [hempty,sub_zero,abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
      exact hpeak.2 ⟨j,hj,rfl⟩
    have hh := hL f f W ∅ (A*E) measured
    rw [hempty,sub_zero,show f i=p by simp [f,isolatedSpiralChannel],abs_of_pos hE] at hh
    change E≤L*(A*E) at hh
    apply (div_le_iff₀ hA).mpr
    exact le_of_mul_le_mul_right (show 1*E≤(L*A)*E by linarith only [hh]) hE

#print axioms receiver_spiral_nodes_injective
#print axioms recover_full_receiver_gram_from_spiral
#print axioms consecutive_spiral_readings_iff_gram
#print axioms spiral_pair_error_bound
#print axioms peak_isolated_spiral_readout
#print axioms sharp_exponential_diagonal_cost

end GaloisForLFunctions.BlackHoleRingdown
