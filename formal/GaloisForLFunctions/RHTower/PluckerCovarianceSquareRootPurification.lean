import GaloisForLFunctions.HTGeometry.FrameOperatorPurity
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCofinalPluckerSpectralOperator
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesSubcriticalPassiveResponse

/-!
# Full physical Plücker covariance and its canonical purification

For history grade `n` and adjacent prime edge `j`, let `M_{n,j}` be the physical Plücker spectral
matrix on the packet `(p_j, n), (p_j, n+1), (p_{j+1}, n), (p_{j+1}, n+1)` and `b_{n,j} > 0` its
normalized block weight.  On the packet presentation `P = ⊕_j ℂ⁴ = ℓ²(ℕ × Fin 4)`:

* **`(PCPOS.1)`–`(PCPOS.2)`** `B_n = ⊕_j b_{n,j} M_{n,j}`, `τ_n = Tr B_n > 0`, and
  `A_n = B_n/τ_n` is positive trace class of trace one.  `B_n` is the frame operator of the rays
  `√(b_{n,j} π_{n,j}(s)) F_{n,j,s}`, where `M_{n,j} = ∑_s π(s) f_s f_sᵀ` is the corpus rank-one
  decomposition of the spectral block into centered node features.
* **`(PCPOS.3)`–`(PCPOS.5)`** the canonical purification `u_n = √A_n ∈ S₂(P)`, realized through
  its columns as `ℓ²(ℕ × Fin 4; P)`, is a unit vector whose partial trace over the column factor
  is `u_n u_n* = A_n`; every edge block of `u_n` is nonzero, so `|u_n⟩⟨u_n|` couples every two
  adjacent-prime edge blocks.
* **`(PCPOS.6)`–`(PCPOS.7)`** `A_0 ≠ A_1`: on edge `0` the kernel lines of `M_{0,0}` and `M_{1,0}`
  are spanned by `(I, 2I, …)` and `(2I, 3I, …)` with `I > 0` the critical Stokes inverse tilt.
  Hence `u_0, u_1` are not collinear and `F₀₁ = |⟨u_0, u_1⟩| = |Tr(√A_0 √A_1)| < 1`.
-/

open Filter Topology
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry

/-- The packet presentation `P = ⊕_j ℂ⁴ = ℓ²(ℕ × Fin 4)`; `(j, i)` is node `i` of edge `j`. -/
abbrev PacketPresentation : Type := lp (fun _ : ℕ × Fin 4 => ℂ) 2

/-- The block weight `b_{n,j}`. -/
def packetWeight (n j : ℕ) : ℝ := gammaSewnCriticalAdjacentPrime_PluckerBlockWeight (n, j)

/-- The spectral block `M_{n,j}`. -/
def packetBlock (n j : ℕ) : Matrix (Fin 4) (Fin 4) ℝ :=
  gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock (n, j)

/-- The selected-pair probabilities `π_{n,j}(s)`. -/
def packetProbability (n j : ℕ) (s : Fin 6) : ℝ :=
  gammaSewnCriticalAdjacentPrime_PluckerProbability (n, j) s

/-- The centered node features `f_{n,j,s}`. -/
def packetFeature (n j : ℕ) (s : Fin 6) (i : Fin 4) : ℝ :=
  gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature (n, j) s i

theorem packetWeight_pos (n j : ℕ) : 0 < packetWeight n j :=
  gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos _

theorem packetProbability_pos (n j : ℕ) (s : Fin 6) : 0 < packetProbability n j s :=
  gammaSewnCriticalAdjacentPrime_PluckerProbability_pos _ s

theorem summable_packetWeight (n : ℕ) : Summable (packetWeight n) :=
  summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight.prod_factor n

theorem packetBlock_eq (n j : ℕ) (i i' : Fin 4) :
    packetBlock n j i i' =
      ∑ s, packetProbability n j s * packetFeature n j s i * packetFeature n j s i' :=
  gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_eq_centered _ i i'

theorem packetBlock_diag_le (n j : ℕ) (i : Fin 4) :
    packetBlock n j i i ≤ gammaSewnCriticalPlucker_nodeBound :=
  (le_abs_self _).trans (gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_abs_le_nodeBound _ i i)

/-! ### Block features and rays -/

/-- The block feature `F_{n,j,s}`: `f_{n,j,s}` placed on edge block `j`. -/
def packetBlockFeature (n j : ℕ) (s : Fin 6) : PacketPresentation :=
  ∑ i : Fin 4, lp.single 2 (j, i) ((packetFeature n j s i : ℝ) : ℂ)

theorem packetBlockFeature_apply (n j : ℕ) (s : Fin 6) (a : ℕ × Fin 4) :
    (packetBlockFeature n j s : ℕ × Fin 4 → ℂ) a =
      if a.1 = j then ((packetFeature n j s a.2 : ℝ) : ℂ) else 0 := by
  rw [packetBlockFeature, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_single, Pi.single_apply]
  rcases a with ⟨j', i⟩
  by_cases h : j' = j
  · subst h
    simp [Prod.ext_iff]
  · simp [Prod.ext_iff, h]

theorem inner_packetBlockFeature (n j : ℕ) (s : Fin 6) (x : PacketPresentation) :
    ⟪packetBlockFeature n j s, x⟫_ℂ =
      ∑ i : Fin 4, ((packetFeature n j s i : ℝ) : ℂ) * (x : ℕ × Fin 4 → ℂ) (j, i) := by
  rw [lp.inner_eq_tsum]
  have hsupp : ∀ a ∉ (Finset.univ.map ⟨fun i : Fin 4 => (j, i), fun _ _ h => (Prod.ext_iff.1 h).2⟩),
      ⟪(packetBlockFeature n j s : ℕ × Fin 4 → ℂ) a, (x : ℕ × Fin 4 → ℂ) a⟫_ℂ = 0 := by
    rintro ⟨j', i⟩ ha
    have hj : j' ≠ j := fun h => ha (Finset.mem_map.2 ⟨i, Finset.mem_univ _, by simp [h]⟩)
    rw [packetBlockFeature_apply, if_neg hj, inner_zero_left]
  rw [tsum_eq_sum hsupp, Finset.sum_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [packetBlockFeature_apply, if_pos rfl, RCLike.inner_apply, Complex.conj_ofReal, mul_comm]

theorem norm_sq_packetBlockFeature (n j : ℕ) (s : Fin 6) :
    ‖packetBlockFeature n j s‖ ^ 2 = ∑ i : Fin 4, packetFeature n j s i ^ 2 := by
  have h := inner_packetBlockFeature n j s (packetBlockFeature n j s)
  rw [inner_self_eq_norm_sq_to_K] at h
  simp only [packetBlockFeature_apply, if_true] at h
  have e1 : ((‖packetBlockFeature n j s‖ ^ 2 : ℝ) : ℂ) = (‖packetBlockFeature n j s‖ : ℂ) ^ 2 := by
    push_cast; rfl
  have h' : ((‖packetBlockFeature n j s‖ ^ 2 : ℝ) : ℂ) =
      ((∑ i : Fin 4, packetFeature n j s i ^ 2 : ℝ) : ℂ) := by
    rw [e1]
    refine h.trans ?_
    push_cast
    simp only [sq]
  exact_mod_cast h'

/-- The ray `√(b_{n,j} π_{n,j}(s)) F_{n,j,s}`. -/
def packetRay (n : ℕ) (js : ℕ × Fin 6) : PacketPresentation :=
  ((Real.sqrt (packetWeight n js.1 * packetProbability n js.1 js.2) : ℝ) : ℂ) •
    packetBlockFeature n js.1 js.2

theorem norm_sq_packetRay (n : ℕ) (js : ℕ × Fin 6) :
    ‖packetRay n js‖ ^ 2 = packetWeight n js.1 * (packetProbability n js.1 js.2 *
      ∑ i : Fin 4, packetFeature n js.1 js.2 i ^ 2) := by
  rw [packetRay, norm_smul, mul_pow, norm_sq_packetBlockFeature, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (mul_pos (packetWeight_pos _ _)
      (packetProbability_pos _ _ _)).le, mul_assoc]

theorem sum_norm_sq_packetRay (n j : ℕ) :
    ∑ s : Fin 6, ‖packetRay n (j, s)‖ ^ 2 =
      packetWeight n j * ∑ i : Fin 4, packetBlock n j i i := by
  simp only [norm_sq_packetRay]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [packetBlock_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

theorem summable_norm_sq_packetRay (n : ℕ) : Summable fun js => ‖packetRay n js‖ ^ 2 := by
  refine (summable_prod_of_nonneg (fun _ => sq_nonneg _)).2 ⟨fun j => Summable.of_finite, ?_⟩
  refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun _ => sq_nonneg _) (fun j => ?_)
    ((summable_packetWeight n).mul_right (4 * gammaSewnCriticalPlucker_nodeBound))
  rw [tsum_fintype, sum_norm_sq_packetRay]
  have hdiag : ∑ i : Fin 4, packetBlock n j i i ≤ 4 * gammaSewnCriticalPlucker_nodeBound := by
    calc ∑ i : Fin 4, packetBlock n j i i ≤ ∑ _i : Fin 4, gammaSewnCriticalPlucker_nodeBound :=
          Finset.sum_le_sum fun i _ => packetBlock_diag_le n j i
      _ = 4 * gammaSewnCriticalPlucker_nodeBound := by simp
  exact mul_le_mul_of_nonneg_left hdiag (packetWeight_pos n j).le

/-- Every packet carries a nonzero ray. -/
theorem exists_packetRay_ne_zero (n j : ℕ) : ∃ s, 0 < ‖packetRay n (j, s)‖ ^ 2 := by
  obtain ⟨i, i', -, hne⟩ :=
    exists_gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_offDiagonal_ne_zero
      (e := n) (gammaSewnCriticalAdjacentPrime_order j)
  have hblock : packetBlock n j i i' ≠ 0 := hne
  rw [packetBlock_eq] at hblock
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hblock
  have hf : packetFeature n j s i ≠ 0 := fun h => hs (by rw [h]; ring)
  refine ⟨s, ?_⟩
  rw [norm_sq_packetRay]
  have hsum : 0 < ∑ k : Fin 4, packetFeature n j s k ^ 2 :=
    lt_of_lt_of_le (pow_pos (abs_pos.2 hf) 2 |>.trans_eq (sq_abs _))
      (Finset.single_le_sum (f := fun k => packetFeature n j s k ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ i))
  exact mul_pos (packetWeight_pos n j) (mul_pos (packetProbability_pos n j s) hsum)

/-- **`(PCPOS.2)`** the trace `τ_n = Tr B_n = ∑_j b_{n,j} Tr M_{n,j}`. -/
def packetTraceMass (n : ℕ) : ℝ := ∑' js, ‖packetRay n js‖ ^ 2

theorem packetTraceMass_pos (n : ℕ) : 0 < packetTraceMass n := by
  obtain ⟨s, hs⟩ := exists_packetRay_ne_zero n 0
  exact (summable_norm_sq_packetRay n).tsum_pos (fun _ => sq_nonneg _) (0, s) hs

/-- **`(PCPOS.1)`** `B_n`, the frame operator of the packet rays. -/
def packetCovariance (n : ℕ) : PacketPresentation →L[ℂ] PacketPresentation :=
  frameOperator (packetRay n)

/-- The normalized rays `τ_n^{-1/2} √(b π) F`. -/
def normalizedPacketRay (n : ℕ) (js : ℕ × Fin 6) : PacketPresentation :=
  (((Real.sqrt (packetTraceMass n))⁻¹ : ℝ) : ℂ) • packetRay n js

theorem norm_sq_normalizedPacketRay (n : ℕ) (js : ℕ × Fin 6) :
    ‖normalizedPacketRay n js‖ ^ 2 = (packetTraceMass n)⁻¹ * ‖packetRay n js‖ ^ 2 := by
  rw [normalizedPacketRay, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    inv_pow, Real.sq_sqrt (packetTraceMass_pos n).le]

theorem summable_norm_sq_normalizedPacketRay (n : ℕ) :
    Summable fun js => ‖normalizedPacketRay n js‖ ^ 2 := by
  simp_rw [norm_sq_normalizedPacketRay]
  exact (summable_norm_sq_packetRay n).mul_left _

theorem tsum_norm_sq_normalizedPacketRay (n : ℕ) :
    ∑' js, ‖normalizedPacketRay n js‖ ^ 2 = 1 := by
  simp_rw [norm_sq_normalizedPacketRay]
  rw [tsum_mul_left, ← packetTraceMass, inv_mul_cancel₀ (packetTraceMass_pos n).ne']

/-- **`(PCPOS.1)`** `A_n = B_n/τ_n`. -/
def normalizedPacketCovariance (n : ℕ) : PacketPresentation →L[ℂ] PacketPresentation :=
  frameOperator (normalizedPacketRay n)

theorem normalizedPacketCovariance_eq (n : ℕ) :
    normalizedPacketCovariance n = ((packetTraceMass n)⁻¹ : ℂ) • packetCovariance n := by
  have hs := summable_norm_sq_packetRay n
  have hs' := summable_norm_sq_normalizedPacketRay n
  ext1 x
  rw [normalizedPacketCovariance, packetCovariance, smul_apply, frameOperator_apply hs',
    frameOperator_apply hs, ← tsum_const_smul'' ((packetTraceMass n)⁻¹ : ℂ)]
  refine tsum_congr fun js => ?_
  rw [normalizedPacketRay, inner_smul_left, smul_smul, smul_smul, Complex.conj_ofReal]
  congr 1
  have hτ := (packetTraceMass_pos n).le
  have hc : (((Real.sqrt (packetTraceMass n))⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt (packetTraceMass n))⁻¹ : ℝ) : ℂ) = ((packetTraceMass n : ℝ) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hτ, Complex.ofReal_inv]
  linear_combination ⟪packetRay n js, x⟫_ℂ * hc

/-- **`(PCPOS.2)`** `A_n ≥ 0`, `A_n ∈ S₁`, `Tr A_n = 1`. -/
theorem normalizedPacketCovariance_density (n : ℕ) :
    (normalizedPacketCovariance n).IsPositive ∧
      MemSchattenClass 1 (normalizedPacketCovariance n) ∧
      opTrace (normalizedPacketCovariance n) = 1 := by
  have hs := summable_norm_sq_normalizedPacketRay n
  refine ⟨frameOperator_isPositive hs, frameOperator_memSchattenClass_one hs, ?_⟩
  rw [normalizedPacketCovariance, opTrace_frameOperator hs, tsum_norm_sq_normalizedPacketRay,
    Complex.ofReal_one]

/-- `B_n ≥ 0`, `B_n ∈ S₁`, `Tr B_n = τ_n`. -/
theorem packetCovariance_traceClass (n : ℕ) :
    (packetCovariance n).IsPositive ∧ MemSchattenClass 1 (packetCovariance n) ∧
      opTrace (packetCovariance n) = packetTraceMass n := by
  have hs := summable_norm_sq_packetRay n
  exact ⟨frameOperator_isPositive hs, frameOperator_memSchattenClass_one hs,
    opTrace_frameOperator hs⟩

/-- **`(PCPOS.1)`, block structure.**  `B_n = ⊕_j b_{n,j} M_{n,j}`:
`(B_n x)(j, i) = b_{n,j} ∑_{i'} M_{n,j}(i, i') x(j, i')`. -/
theorem packetCovariance_apply (n : ℕ) (x : PacketPresentation) (j : ℕ) (i : Fin 4) :
    (packetCovariance n x : ℕ × Fin 4 → ℂ) (j, i) =
      ((packetWeight n j : ℝ) : ℂ) *
        ∑ i' : Fin 4, ((packetBlock n j i i' : ℝ) : ℂ) * (x : ℕ × Fin 4 → ℂ) (j, i') := by
  have hs := summable_norm_sq_packetRay n
  have hsum : Summable fun js => ⟪packetRay n js, x⟫_ℂ • packetRay n js :=
    (Summable.of_norm (summable_norm_rankOne_frame hs)).mapL (ContinuousLinearMap.apply ℂ _ x)
  rw [packetCovariance, frameOperator_apply hs]
  have hev : ∀ f : PacketPresentation,
      lp.evalCLM ℂ (fun _ : ℕ × Fin 4 => ℂ) 2 (j, i) f = (f : ℕ × Fin 4 → ℂ) (j, i) :=
    fun _ => rfl
  have heval := (lp.evalCLM ℂ (fun _ : ℕ × Fin 4 => ℂ) 2 (j, i)).map_tsum hsum
  rw [hev] at heval
  rw [heval]
  have hsupp : ∀ js ∉
      (Finset.univ.map ⟨fun s : Fin 6 => (j, s), fun _ _ h => (Prod.ext_iff.1 h).2⟩),
      (lp.evalCLM ℂ (fun _ : ℕ × Fin 4 => ℂ) 2 (j, i)) (⟪packetRay n js, x⟫_ℂ • packetRay n js) =
        0 := by
    rintro ⟨j', s⟩ hjs
    have hj : j' ≠ j := fun h => hjs (Finset.mem_map.2 ⟨s, Finset.mem_univ _, by simp [h]⟩)
    rw [hev, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, packetRay, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, packetBlockFeature_apply, if_neg (Ne.symm hj), mul_zero,
      mul_zero]
  rw [tsum_eq_sum hsupp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, hev, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  have hterm : ∀ s : Fin 6,
      ⟪packetRay n (j, s), x⟫_ℂ * (packetRay n (j, s) : ℕ × Fin 4 → ℂ) (j, i) =
      ((packetWeight n j : ℝ) : ℂ) * ∑ i' : Fin 4,
        ((packetProbability n j s * packetFeature n j s i * packetFeature n j s i' : ℝ) : ℂ) *
          (x : ℕ × Fin 4 → ℂ) (j, i') := fun s => by
    have hc : ((Real.sqrt (packetWeight n j * packetProbability n j s) : ℝ) : ℂ) *
        ((Real.sqrt (packetWeight n j * packetProbability n j s) : ℝ) : ℂ) =
        ((packetWeight n j : ℝ) : ℂ) * ((packetProbability n j s : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (mul_pos (packetWeight_pos n j)
        (packetProbability_pos n j s)).le, Complex.ofReal_mul]
    simp only [packetRay, inner_smul_left, Complex.conj_ofReal, inner_packetBlockFeature,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, packetBlockFeature_apply]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i' _ => ?_
    push_cast
    linear_combination (↑(packetFeature n j s i') * (x : ℕ × Fin 4 → ℂ) (j, i') *
      ↑(packetFeature n j s i)) * hc
  rw [Finset.sum_congr rfl fun s _ => hterm s, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [← Finset.sum_mul, packetBlock_eq]
  push_cast
  rfl

/-- **`(PCPOS.1)`** the block structure of `A_n = B_n/τ_n`. -/
theorem normalizedPacketCovariance_apply (n : ℕ) (x : PacketPresentation) (j : ℕ) (i : Fin 4) :
    (normalizedPacketCovariance n x : ℕ × Fin 4 → ℂ) (j, i) =
      ((packetWeight n j / packetTraceMass n : ℝ) : ℂ) *
        ∑ i' : Fin 4, ((packetBlock n j i i' : ℝ) : ℂ) * (x : ℕ × Fin 4 → ℂ) (j, i') := by
  rw [normalizedPacketCovariance_eq, smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    packetCovariance_apply, Complex.ofReal_div]
  ring

/-! ### `(PCPOS.6)`–`(PCPOS.7)`: the polarizations move -/

/-- The kernel vector of a physical packet is the vector of Stokes gaps of its four cells. -/
theorem packetKernelVector_apply (e j : ℕ) (i : Fin 4) :
    gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (e, j) i =
      RHTower.gammaSewnMobiusApertureStokesGap (1 / 2)
        (gammaSewnOrderedPrimeDepthPlucker_cell e (gammaSewnCriticalAdjacentPrime_lower j)
          (gammaSewnCriticalAdjacentPrime_upper j) i) := by
  have hgap : 0 < RHTower.gammaSewnMobiusApertureStokesGap (1 / 2)
      (gammaSewnOrderedPrimeDepthPlucker_cell e (gammaSewnCriticalAdjacentPrime_lower j)
        (gammaSewnCriticalAdjacentPrime_upper j) i) :=
    RHTower.gammaSewnMobiusApertureStokesGap_pos (by norm_num) _
  simp only [gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector,
    gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector,
    gammaSewnCriticalPrimeDepthPacket_node,
    RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode,
    RHTower.gammaSewnMobiusApertureStokesReciprocalGapNode]
  rw [Real.sqrt_sq (inv_nonneg.2 hgap.le), inv_inv]

/-- **`(PCPOS.7)`** on edge `j` the kernel line at depth `0` is spanned by `(I, 2I, …)` and at
depth `1` by `(2I, 3I, …)`, `I` the critical Stokes inverse tilt of `p_j`; they differ. -/
theorem packetKernelVector_depth_zero_one (j : ℕ) :
    gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (0, j) 0 =
        RHTower.gammaSewnMobiusApertureStokesInverseTilt (1 / 2)
          (gammaSewnCriticalAdjacentPrime_lower j) ∧
      gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (0, j) 1 =
        2 * RHTower.gammaSewnMobiusApertureStokesInverseTilt (1 / 2)
          (gammaSewnCriticalAdjacentPrime_lower j) ∧
      gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (1, j) 0 =
        2 * RHTower.gammaSewnMobiusApertureStokesInverseTilt (1 / 2)
          (gammaSewnCriticalAdjacentPrime_lower j) ∧
      gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (1, j) 1 =
        3 * RHTower.gammaSewnMobiusApertureStokesInverseTilt (1 / 2)
          (gammaSewnCriticalAdjacentPrime_lower j) := by
  simp only [packetKernelVector_apply, gammaSewnOrderedPrimeDepthPlucker_cell,
    RHTower.gammaSewnMobiusApertureStokesGap, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

theorem packetKernelVector_not_proportional (j : ℕ) (c : ℝ) :
    gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (1, j) ≠
      c • gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (0, j) := by
  intro h
  obtain ⟨h0, h1, h2, h3⟩ := packetKernelVector_depth_zero_one j
  have hI := RHTower.gammaSewnMobiusApertureStokesInverseTilt_pos (s := 1 / 2) (by norm_num)
    (gammaSewnCriticalAdjacentPrime_lower j)
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  simp only [Pi.smul_apply, smul_eq_mul] at e0 e1
  rw [h2, h0] at e0
  rw [h3, h1] at e1
  have hc : c = 2 := by
    have := mul_right_cancel₀ hI.ne' (by linarith : 2 * _ = c * _)
    exact this.symm
  subst hc
  nlinarith

/-- The block of edge `j` of the vector `v` placed on that edge. -/
def packetEdgeVector (j : ℕ) (v : Fin 4 → ℝ) : PacketPresentation :=
  ∑ i : Fin 4, lp.single 2 (j, i) ((v i : ℝ) : ℂ)

theorem packetEdgeVector_apply_same (j : ℕ) (v : Fin 4 → ℝ) (i : Fin 4) :
    (packetEdgeVector j v : ℕ × Fin 4 → ℂ) (j, i) = ((v i : ℝ) : ℂ) := by
  rw [packetEdgeVector, lp.coeFn_sum, Finset.sum_apply]
  simp [Pi.single_apply, Prod.ext_iff]

/-- **`(PCPOS.6)`** the normalized covariances at depths zero and one differ. -/
theorem normalizedPacketCovariance_zero_ne_one :
    normalizedPacketCovariance 0 ≠ normalizedPacketCovariance 1 := by
  intro h
  set v := gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (1, 0)
  have hker : (packetBlock 1 0).mulVec v = 0 :=
    gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector_mulVec_eq_zero (1, 0)
  have hzero : (packetBlock 0 0).mulVec v = 0 := by
    funext i
    have hx := congrArg (fun A => (A (packetEdgeVector 0 v) : ℕ × Fin 4 → ℂ) (0, i)) h
    simp only [normalizedPacketCovariance_apply, packetEdgeVector_apply_same] at hx
    have h1 : ∑ i' : Fin 4, ((packetBlock 1 0 i i' : ℝ) : ℂ) * ((v i' : ℝ) : ℂ) = 0 := by
      have := congrFun hker i
      rw [Matrix.mulVec, dotProduct] at this
      exact_mod_cast this
    rw [h1, mul_zero] at hx
    have hw : ((packetWeight 0 0 / packetTraceMass 0 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (div_pos (packetWeight_pos 0 0) (packetTraceMass_pos 0)).ne'
    have h0 := (mul_eq_zero.1 hx).resolve_left hw
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply]
    exact_mod_cast h0
  have hspan :=
    (gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_mulVec_eq_zero_iff_smul_kernel
      (e := 0) (gammaSewnCriticalAdjacentPrime_order 0) v).1 hzero
  obtain ⟨c, hc⟩ := hspan
  exact packetKernelVector_not_proportional 0 c hc

/-! ### `(PCPOS.3)`–`(PCPOS.5)`: the canonical purification `√A_n ∈ S₂(P)` -/

/-- `√A_n`. -/
def sqrtPacketCovariance (n : ℕ) : PacketPresentation →L[ℂ] PacketPresentation :=
  positiveSqrt (normalizedPacketCovariance n)

theorem sqrtPacketCovariance_isPositive (n : ℕ) : (sqrtPacketCovariance n).IsPositive :=
  positiveSqrt_isPositive _

theorem sqrtPacketCovariance_mul_self (n : ℕ) :
    sqrtPacketCovariance n ∘L sqrtPacketCovariance n = normalizedPacketCovariance n :=
  positiveSqrt_comp_self (normalizedPacketCovariance_density n).1

theorem adjoint_sqrtPacketCovariance (n : ℕ) :
    adjoint (sqrtPacketCovariance n) = sqrtPacketCovariance n :=
  (sqrtPacketCovariance_isPositive n).isSelfAdjoint.adjoint_eq

/-- `‖√A_n e‖² = ‖W_n* e‖²`, `W_n` the synthesis of the normalized rays (`A_n = W_n W_n*`). -/
theorem norm_sq_sqrtPacketCovariance_apply (n : ℕ) (e : PacketPresentation) :
    ‖sqrtPacketCovariance n e‖ ^ 2 =
      ‖adjoint (squareSummableSynthesis (normalizedPacketRay n)
        (summable_norm_sq_normalizedPacketRay n)) e‖ ^ 2 := by
  set W := squareSummableSynthesis (normalizedPacketRay n) (summable_norm_sq_normalizedPacketRay n)
  have hA : normalizedPacketCovariance n = W ∘L adjoint W :=
    frameOperator_eq_leftGram (summable_norm_sq_normalizedPacketRay n)
  have h1 : ((‖sqrtPacketCovariance n e‖ ^ 2 : ℝ) : ℂ) =
      ⟪e, normalizedPacketCovariance n e⟫_ℂ := by
    have hs := adjoint_inner_right (sqrtPacketCovariance n) e (sqrtPacketCovariance n e)
    rw [adjoint_sqrtPacketCovariance] at hs
    rw [← sqrtPacketCovariance_mul_self, comp_apply, hs, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have h2 : ((‖adjoint W e‖ ^ 2 : ℝ) : ℂ) = ⟪e, normalizedPacketCovariance n e⟫_ℂ := by
    rw [hA, comp_apply, ← adjoint_inner_left, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  exact_mod_cast h1.trans h2.symm

/-- The basis of `P`. -/
abbrev packetBasis : HilbertBasis (ℕ × Fin 4) ℂ PacketPresentation := HilbertSchmidt.lpBasis _

theorem summable_norm_sq_sqrtPacketCovariance_basis (n : ℕ) :
    Summable fun k => ‖sqrtPacketCovariance n (packetBasis k)‖ ^ 2 := by
  have hW := squareSummableSynthesis_isHilbertSchmidt (summable_norm_sq_normalizedPacketRay n)
  simp_rw [norm_sq_sqrtPacketCovariance_apply]
  exact hW.adjoint.summable packetBasis

theorem tsum_norm_sq_sqrtPacketCovariance_basis (n : ℕ) :
    ∑' k, ‖sqrtPacketCovariance n (packetBasis k)‖ ^ 2 = 1 := by
  have hW := squareSummableSynthesis_isHilbertSchmidt (summable_norm_sq_normalizedPacketRay n)
  simp_rw [norm_sq_sqrtPacketCovariance_apply]
  rw [← hsNormSq_eq hW.adjoint packetBasis, hW.hsNormSq_adjoint,
    hsNormSq_squareSummableSynthesis, tsum_norm_sq_normalizedPacketRay]

/-- The Hilbert–Schmidt carrier `E = S₂(P)`, realized by columns as `ℓ²(ℕ × Fin 4; P)`. -/
abbrev PacketHilbertSchmidt : Type := lp (fun _ : ℕ × Fin 4 => PacketPresentation) 2

/-- **`(PCPOS.3)`** the canonical purification `u_n = √A_n ∈ S₂(P)` (columns `√A_n e_k`). -/
def purifiedCovariance (n : ℕ) : PacketHilbertSchmidt :=
  framePurification (fun k => sqrtPacketCovariance n (packetBasis k))
    (summable_norm_sq_sqrtPacketCovariance_basis n)

@[simp] theorem purifiedCovariance_apply (n : ℕ) (k : ℕ × Fin 4) :
    purifiedCovariance n k = sqrtPacketCovariance n (packetBasis k) := rfl

/-- **`(PCPOS.4)`** `‖u_n‖₂² = Tr A_n = 1`. -/
theorem norm_purifiedCovariance (n : ℕ) : ‖purifiedCovariance n‖ = 1 := by
  have h := norm_sq_framePurification (summable_norm_sq_sqrtPacketCovariance_basis n)
  rw [tsum_norm_sq_sqrtPacketCovariance_basis] at h
  change ‖purifiedCovariance n‖ ^ 2 = 1 at h
  have h0 := norm_nonneg (purifiedCovariance n)
  nlinarith [sq_nonneg (‖purifiedCovariance n‖ - 1)]

/-- The Hilbert–Schmidt pairing `⟨u_n, u_m⟩ = Tr(√A_n √A_m) = ∑_k ⟨√A_n e_k, √A_m e_k⟩`. -/
theorem inner_purifiedCovariance (n m : ℕ) :
    ⟪purifiedCovariance n, purifiedCovariance m⟫_ℂ =
      ∑' k, ⟪sqrtPacketCovariance n (packetBasis k), sqrtPacketCovariance m (packetBasis k)⟫_ℂ :=
  lp.inner_eq_tsum _ _

/-- The frame operator of the columns of `S` is `S S*`. -/
theorem frameOperator_columns {S : PacketPresentation →L[ℂ] PacketPresentation}
    (hS : Summable fun k => ‖S (packetBasis k)‖ ^ 2) :
    frameOperator (fun k => S (packetBasis k)) = S ∘L adjoint S := by
  ext1 x
  rw [frameOperator_apply hS, comp_apply]
  have h := (packetBasis.hasSum_repr (adjoint S x)).mapL S
  simp only [map_smul, HilbertBasis.repr_apply_apply] at h
  rw [← h.tsum_eq]
  refine tsum_congr fun k => ?_
  rw [adjoint_inner_right]

/-- **`(PCPOS.5)`** the partial trace of `|u_n⟩⟨u_n|` over the column factor is
`u_n u_n* = A_n`. -/
theorem purifiedCovariance_isPartialTrace (n : ℕ) :
    IsPartialTrace (rankOne ℂ (purifiedCovariance n) (purifiedCovariance n))
      (normalizedPacketCovariance n) := by
  have h := frameOperator_isPartialTrace (summable_norm_sq_sqrtPacketCovariance_basis n)
  rwa [frameOperator_columns (summable_norm_sq_sqrtPacketCovariance_basis n),
    adjoint_sqrtPacketCovariance, sqrtPacketCovariance_mul_self] at h

/-! ### Non-collinearity and the fidelity gap -/

theorem sqrtPacketCovariance_eq_of_purified {n m : ℕ} {c : ℂ}
    (h : purifiedCovariance m = c • purifiedCovariance n) :
    sqrtPacketCovariance m = c • sqrtPacketCovariance n := by
  refine ContinuousLinearMap.ext_on (s := Set.range packetBasis)
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr packetBasis.dense_span) ?_
  rintro _ ⟨k, rfl⟩
  have := congrArg (fun u : PacketHilbertSchmidt => u k) h
  simpa using this

/-- **`(PCPOS.6)`** `u_0` and `u_1` are not collinear. -/
theorem purifiedCovariance_not_collinear (c : ℂ) :
    purifiedCovariance 1 ≠ c • purifiedCovariance 0 := by
  intro h
  have hS := sqrtPacketCovariance_eq_of_purified h
  have hA : normalizedPacketCovariance 1 = (c * c) • normalizedPacketCovariance 0 := by
    rw [← sqrtPacketCovariance_mul_self, ← sqrtPacketCovariance_mul_self, hS, smul_comp,
      comp_smul, smul_smul]
  have htr := congrArg opTrace hA
  rw [opTrace_smul, (normalizedPacketCovariance_density 1).2.2,
    (normalizedPacketCovariance_density 0).2.2, mul_one] at htr
  rw [← htr, one_smul] at hA
  exact normalizedPacketCovariance_zero_ne_one hA.symm

/-- **`(PCPOS.6)`** the fidelity `F₀₁ = |Tr(√A_0 √A_1)| = |⟨u_0, u_1⟩|` is strictly below one. -/
theorem fidelity_lt_one : ‖⟪purifiedCovariance 0, purifiedCovariance 1⟫_ℂ‖ < 1 := by
  have hle := norm_inner_le_norm (𝕜 := ℂ) (purifiedCovariance 0) (purifiedCovariance 1)
  rw [norm_purifiedCovariance, norm_purifiedCovariance, one_mul] at hle
  refine lt_of_le_of_ne hle fun heq => ?_
  have h0 : purifiedCovariance 0 ≠ 0 := by
    intro h; have := norm_purifiedCovariance 0; rw [h, norm_zero] at this; exact zero_ne_one this
  have h1 : purifiedCovariance 1 ≠ 0 := by
    intro h; have := norm_purifiedCovariance 1; rw [h, norm_zero] at this; exact zero_ne_one this
  have heq' : ‖⟪purifiedCovariance 0, purifiedCovariance 1⟫_ℂ‖ =
      ‖purifiedCovariance 0‖ * ‖purifiedCovariance 1‖ := by
    rw [heq, norm_purifiedCovariance, norm_purifiedCovariance, one_mul]
  obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff h0 h1).1 heq'
  exact purifiedCovariance_not_collinear r hr

/-! ### Prime mixing inside the purification -/

/-- Every edge block of `u_n` is nonzero. -/
theorem exists_purifiedCovariance_edge_ne_zero (n j : ℕ) :
    ∃ k : ℕ × Fin 4, ∃ i : Fin 4, (purifiedCovariance n k : ℕ × Fin 4 → ℂ) (j, i) ≠ 0 := by
  by_contra! hall
  -- the rows of edge `j` of `√A_n` vanish, so `√A_n e_{(j,i)} = 0` and `A_n e_{(j,i)} = 0`
  have hcol : ∀ i : Fin 4, sqrtPacketCovariance n (packetBasis (j, i)) = 0 := fun i => by
    refine packetBasis.repr.injective ?_
    ext k
    rw [map_zero, HilbertBasis.repr_apply_apply, lp.coeFn_zero, Pi.zero_apply,
      ← adjoint_inner_left, adjoint_sqrtPacketCovariance, ← inner_conj_symm,
      ← purifiedCovariance_apply]
    have hji : packetBasis (j, i) = lp.single 2 (j, i) (1 : ℂ) := HilbertSchmidt.lpBasis_apply _
    rw [hji, lp.inner_single_left, hall k i, inner_zero_right, map_zero]
  have hA : ∀ i : Fin 4, normalizedPacketCovariance n (packetBasis (j, i)) = 0 := fun i => by
    rw [← sqrtPacketCovariance_mul_self, comp_apply, hcol i, map_zero]
  obtain ⟨i, i', -, hne⟩ :=
    exists_gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_offDiagonal_ne_zero
      (e := n) (gammaSewnCriticalAdjacentPrime_order j)
  have hblock : packetBlock n j i i' ≠ 0 := hne
  have hx := congrArg (fun x : PacketPresentation => (x : ℕ × Fin 4 → ℂ) (j, i)) (hA i')
  simp only [normalizedPacketCovariance_apply, lp.coeFn_zero, Pi.zero_apply,
    HilbertSchmidt.lpBasis_apply, lp.single_apply] at hx
  rw [Finset.sum_eq_single i'] at hx
  · simp only [Pi.single_eq_same, mul_one] at hx
    have hw : ((packetWeight n j / packetTraceMass n : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (div_pos (packetWeight_pos n j) (packetTraceMass_pos n)).ne'
    have := (mul_eq_zero.1 hx).resolve_left hw
    exact hblock (by exact_mod_cast this)
  · intro b _ hb
    simp [Prod.ext_iff, hb]
  · simp

/-- **§2, prime mixing**: `|u_n⟩⟨u_n|` has a nonzero matrix coefficient between Hilbert–Schmidt
coordinates of any two adjacent-prime edge blocks `j, j'`. -/
theorem exists_purified_crossEdge_coefficient_ne_zero (n j j' : ℕ) :
    ∃ (k k' : ℕ × Fin 4) (i i' : Fin 4),
      ⟪(lp.single 2 k (lp.single 2 (j, i) (1 : ℂ) : PacketPresentation) :
          PacketHilbertSchmidt),
        rankOne ℂ (purifiedCovariance n) (purifiedCovariance n)
          (lp.single 2 k' (lp.single 2 (j', i') (1 : ℂ) : PacketPresentation))⟫_ℂ ≠ 0 := by
  obtain ⟨k, i, hki⟩ := exists_purifiedCovariance_edge_ne_zero n j
  obtain ⟨k', i', hki'⟩ := exists_purifiedCovariance_edge_ne_zero n j'
  refine ⟨k, k', i, i', ?_⟩
  rw [rankOne_apply, inner_smul_right, lp.inner_single_left, lp.inner_single_right,
    lp.inner_single_left, lp.inner_single_right]
  simp only [RCLike.inner_apply, map_one, mul_one, one_mul]
  exact mul_ne_zero (by simpa using hki') hki

end RHTower.HedenmalmThetaSource
