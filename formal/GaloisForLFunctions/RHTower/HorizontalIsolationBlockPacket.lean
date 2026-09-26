import GaloisForLFunctions.HilbertMetric.HorizontalLamzouriUnnormalized
import GaloisForLFunctions.RHTower.WindowTransformSamplingParseval

/-!
# The sampled Weil matrix as a horizontal packet

The multiplicity-aware zero-side matrix of Zeta23, normalised by `c`, is
`Σ_{on-line} m u uᵀ/c + Σ_{pairs} 2m (x xᵀ − y yᵀ)/c` with real vectors `u` (on-line), `x = Re u`,
`y = Im u` (`blockA_apply_split`).  Split the simple on-line points `S₁` into a set `M` and its
complement.  Then the matrix is the coordinate kernel of the horizontal packet
(multiple on-line points `S₂`, horizontally simple `S₁ \ M`, mixed `M`, pairs `R`) in
`EuclideanSpace ℝ d` (`blockP_add_blockQ_eq_kernel`).  Its trace is the packet mass, its
Frobenius norm is the packet energy, and `N` is the packet count.

The unnormalised horizontal Lamzouri inequality then gives
`4 tr − ‖·‖² − 2N ≤ #(S₁ \ M)` as soon as every point of `M` lies within `1/8` of the real vector
of some pair (`horizontal_block_count`).  This is Zeta23's `c = 2` count `≤ s₁` with the mixed
points removed.
-/

open scoped RealInnerProductSpace
open Finset Matrix

namespace RHTower

noncomputable section

open GaloisForLFunctions.HilbertMetric

section Coordinates

set_option linter.unusedSectionVars false

variable {d : Type*} [Fintype d]
variable {ι₂ ιH ιM ιP : Type*} [Fintype ι₂] [Fintype ιH] [Fintype ιM] [Fintype ιP]
variable (P : HorizontalPacket (EuclideanSpace ℝ d) ι₂ ιH ιM ιP)

/-- The kernel `Σ_a c_a w_a(k) w_a(l)` of a packet in coordinates. -/
def packetKernel (k l : d) : ℝ := ∑ a, P.wt a * (P.vec a k * P.vec a l)

theorem inner_vec_sq (a b : ι₂ ⊕ ιH ⊕ ιM ⊕ ιP ⊕ ιP) :
    ⟪P.vec a, P.vec b⟫ ^ 2 = ∑ k, ∑ l, (P.vec a k * P.vec b k) * (P.vec a l * P.vec b l) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem energy_eq_sum_packetKernel_sq :
    P.energy = ∑ k, ∑ l, packetKernel P k l ^ 2 := by
  unfold HorizontalPacket.energy packetKernel
  set x := P.vec
  set c := P.wt
  calc ∑ a, ∑ b, c a * c b * ⟪x a, x b⟫ ^ 2
      = ∑ a, ∑ b, ∑ k, ∑ l, (c a * (x a k * x a l)) * (c b * (x b k * x b l)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [inner_vec_sq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
    _ = ∑ a, ∑ k, ∑ b, ∑ l, (c a * (x a k * x a l)) * (c b * (x b k * x b l)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, ∑ l, (c a * (x a k * x a l)) * (c b * (x b k * x b l)) :=
        Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ l, ∑ b, (c a * (x a k * x a l)) * (c b * (x b k * x b l)) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ a, ∑ b, (c a * (x a k * x a l)) * (c b * (x b k * x b l)) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ l, (∑ a, c a * (x a k * x a l)) ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [sq, Finset.sum_mul_sum]

theorem mass_eq_sum_packetKernel_diag :
    P.mass = ∑ k, packetKernel P k k := by
  unfold HorizontalPacket.mass packetKernel
  simp_rw [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
  ring

end Coordinates

section Block

set_option linter.unusedSectionVars false

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : Zeta23.ZeroSide.ZeroBlockData ι d) (Pr : D.PairReps) (c : ℝ) (M : Finset ι)

/-- The real part of a block vector, scaled by `1/√c`. -/
def blockReVec (z : ι) : EuclideanSpace ℝ d :=
  WithLp.toLp 2 (fun k => (D.v z k).re / Real.sqrt c)

/-- The imaginary part of a block vector, scaled by `1/√c`. -/
def blockImVec (z : ι) : EuclideanSpace ℝ d :=
  WithLp.toLp 2 (fun k => (D.v z k).im / Real.sqrt c)

/-- The horizontal packet of the block data: multiple on-line points `S₂`, horizontally simple
points `S₁ \ M`, mixed points `M`, and the off-line pairs `R`. -/
def blockPacket : HorizontalPacket (EuclideanSpace ℝ d) {z // z ∈ D.S₂} {z // z ∈ D.S₁ \ M}
    {z // z ∈ M} {z // z ∈ Pr.R} where
  f₂ z := blockReVec D c z
  m₂ z := D.m z
  fH z := blockReVec D c z
  fM z := blockReVec D c z
  g p := blockReVec D c p
  h p := blockImVec D c p
  mP p := D.m p

theorem blockA_apply_split (k l : d) :
    D.blockA k l = ((∑ z ∈ D.onLine, (D.m z : ℝ) * ((D.v z k).re * (D.v z l).re)
      + ∑ z ∈ Pr.R, 2 * (D.m z : ℝ) * ((D.v z k).re * (D.v z l).re - (D.v z k).im * (D.v z l).im)
      : ℝ) : ℂ) := by
  rw [D.blockA_apply, D.sum_split Pr]
  push_cast
  congr 1
  · refine Finset.sum_congr rfl fun z hz => ?_
    have hreal : star (D.v z) = D.v z := D.star_v_of_onLine ((D.mem_onLine).mp hz)
    have hk : D.v z k = ((D.v z k).re : ℂ) := by
      have := congrFun hreal k
      simp only [Pi.star_apply, RCLike.star_def] at this
      exact (Complex.conj_eq_iff_re.mp this).symm
    have hl : D.v z l = ((D.v z l).re : ℂ) := by
      have := congrFun hreal l
      simp only [Pi.star_apply, RCLike.star_def] at this
      exact (Complex.conj_eq_iff_re.mp this).symm
    conv_lhs => rw [hk, hl]
  · refine Finset.sum_congr rfl fun z _ => ?_
    rw [D.m_σ, D.v_σ]
    simp only [Pi.star_apply, RCLike.star_def]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem blockReVec_apply (z : ι) (k : d) : blockReVec D c z k = (D.v z k).re / Real.sqrt c := by
  simp [blockReVec]

theorem blockImVec_apply (z : ι) (k : d) : blockImVec D c z k = (D.v z k).im / Real.sqrt c := by
  simp [blockImVec]

/-- **The sampled matrix is the packet kernel.** -/
theorem blockP_add_blockQ_apply (hc : 0 < c) (hM : M ⊆ D.S₁) (k l : d) :
    (D.blockP c + D.blockQ c) k l = ((packetKernel (blockPacket D Pr c M) k l : ℝ) : ℂ) := by
  rw [D.blockP_add_blockQ, Matrix.smul_apply, blockA_apply_split D Pr, smul_eq_mul,
    ← Complex.ofReal_mul]
  congr 1
  have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  have hsc : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hprod : ∀ x y : ℝ, x / Real.sqrt c * (y / Real.sqrt c) = c⁻¹ * (x * y) := fun x y => by
    field_simp; rw [Real.sq_sqrt hc.le]; ring
  unfold packetKernel
  rw [(blockPacket D Pr c M).sum_wt_mul (fun v => v k * v l)]
  simp only [blockPacket, blockReVec_apply, blockImVec_apply, hprod]
  simp only [Finset.sum_coe_sort (s := D.S₂) (f := fun z => (D.m z : ℝ) * (c⁻¹ * ((D.v z k).re * (D.v z l).re))),
    Finset.sum_coe_sort (s := D.S₁ \ M) (f := fun z => c⁻¹ * ((D.v z k).re * (D.v z l).re)),
    Finset.sum_coe_sort (s := M) (f := fun z => c⁻¹ * ((D.v z k).re * (D.v z l).re)),
    Finset.sum_coe_sort (s := Pr.R) (f := fun z => 2 * (D.m z : ℝ) * (c⁻¹ * ((D.v z k).re * (D.v z l).re))),
    Finset.sum_coe_sort (s := Pr.R) (f := fun z => 2 * (D.m z : ℝ) * (c⁻¹ * ((D.v z k).im * (D.v z l).im)))]
  -- on-line split
  have hon : ∑ z ∈ D.onLine, (D.m z : ℝ) * ((D.v z k).re * (D.v z l).re)
      = ∑ z ∈ D.S₂, (D.m z : ℝ) * ((D.v z k).re * (D.v z l).re)
        + ∑ z ∈ D.S₁ \ M, (D.v z k).re * (D.v z l).re + ∑ z ∈ M, (D.v z k).re * (D.v z l).re := by
    rw [D.onLine_eq_S₁_union_S₂, Finset.sum_union D.disjoint_S₁_S₂]
    have hS1 : D.S₁ = (D.S₁ \ M) ∪ M := (Finset.sdiff_union_of_subset hM).symm
    have hm1 : ∀ z ∈ D.S₁, (D.m z : ℝ) = 1 := fun z hz => by
      have := (Finset.mem_filter.mp hz).2.2
      exact_mod_cast this
    rw [Finset.sum_congr rfl fun z hz => by rw [hm1 z hz, one_mul]]
    conv_lhs => rw [hS1]
    rw [Finset.sum_union Finset.sdiff_disjoint]
    ring
  rw [hon, mul_add, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_ <;>
    exact Finset.sum_congr rfl fun z _ => by ring

omit [Fintype ι] [DecidableEq ι] in
theorem frobSq_ofReal_matrix (r : d → d → ℝ) :
    RHLinalg.frobSq (fun k l => ((r k l : ℝ) : ℂ) : Matrix d d ℂ) = ∑ k, ∑ l, r k l ^ 2 := by
  simp only [RHLinalg.frobSq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_ofReal, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re, sq]

omit [Fintype ι] [DecidableEq ι] in
theorem rtrace_ofReal_matrix (r : d → d → ℝ) :
    RHLinalg.rtrace (fun k l => ((r k l : ℝ) : ℂ) : Matrix d d ℂ) = ∑ k, r k k := by
  simp [RHLinalg.rtrace, Matrix.trace, Matrix.diag]

theorem blockP_add_blockQ_eq_kernel (hc : 0 < c) (hM : M ⊆ D.S₁) :
    D.blockP c + D.blockQ c
      = (fun k l => ((packetKernel (blockPacket D Pr c M) k l : ℝ) : ℂ) : Matrix d d ℂ) := by
  ext k l
  exact blockP_add_blockQ_apply D Pr c M hc hM k l

theorem blockPacket_count (hM : M ⊆ D.S₁) :
    (blockPacket D Pr c M).count = (D.Ncount : ℝ) := by
  simp only [HorizontalPacket.count, blockPacket, Fintype.card_coe]
  rw [Finset.sum_coe_sort (s := D.S₂) (f := fun z => (D.m z : ℝ)),
    Finset.sum_coe_sort (s := Pr.R) (f := fun z => (D.m z : ℝ))]
  have hN : (D.Ncount : ℝ) = ∑ z ∈ D.onLine, (D.m z : ℝ) + ∑ z ∈ Pr.R, ((D.m z : ℝ) + D.m (D.σ z)) := by
    unfold Zeta23.ZeroSide.ZeroBlockData.Ncount
    push_cast
    exact D.sum_split Pr (fun z => (D.m z : ℝ))
  rw [hN]
  simp only [D.m_σ]
  rw [D.onLine_eq_S₁_union_S₂, Finset.sum_union D.disjoint_S₁_S₂]
  have hm1 : ∀ z ∈ D.S₁, (D.m z : ℝ) = 1 := fun z hz => by
    have := (Finset.mem_filter.mp hz).2.2
    exact_mod_cast this
  rw [Finset.sum_congr rfl hm1, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (D.S₁.card : ℝ) = ((D.S₁ \ M).card : ℝ) + (M.card : ℝ) := by
    rw [← Nat.cast_add, Finset.card_sdiff_add_card_eq_card hM]
  rw [hcard, Finset.mul_sum]
  simp only [← two_mul]
  ring

theorem norm_blockReVec_le_one (hc : 0 < c) {z : ι} (hz : ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    ‖blockReVec D c z‖ ≤ 1 := by
  have hsq : ‖blockReVec D c z‖ ^ 2 ≤ 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [blockReVec_apply, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hc.le]
    rw [← Finset.sum_div, div_le_one hc]
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) hz
    have := Complex.abs_re_le_norm (D.v z k)
    have h0 := abs_nonneg (D.v z k).re
    rw [← sq_abs]
    exact pow_le_pow_left₀ h0 this 2
  have h0 := norm_nonneg (blockReVec D c z)
  nlinarith

/-- **Horizontal count at the block level.**  If every point of `M ⊆ S₁` lies within `1/8` of the
real vector of some off-line pair, then `4 tr − ‖·‖² − 2N ≤ #(S₁ \ M)` for the normalised block
matrix. -/
theorem horizontal_block_count (hc : 0 < c) (hM : M ⊆ D.S₁)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c)
    (σ : {z // z ∈ M} → {z // z ∈ Pr.R})
    (hnear : ∀ x : {z // z ∈ M}, ‖blockReVec D c (σ x) - blockReVec D c x‖ ≤ 1 / 8) :
    4 * RHLinalg.rtrace (D.blockP c + D.blockQ c) - RHLinalg.frobSq (D.blockP c + D.blockQ c)
      - 2 * (D.Ncount : ℝ) ≤ ((D.S₁ \ M).card : ℝ) := by
  set Pk := blockPacket D Pr c M
  rw [blockP_add_blockQ_eq_kernel D Pr c M hc hM, frobSq_ofReal_matrix, rtrace_ofReal_matrix,
    ← energy_eq_sum_packetKernel_sq, ← mass_eq_sum_packetKernel_diag,
    ← blockPacket_count D Pr c M hM]
  have hS1on : ∀ z ∈ D.S₁, z ∈ D.onLine := fun z hz => by
    rw [D.onLine_eq_S₁_union_S₂]; exact Finset.mem_union_left _ hz
  have h := Pk.four_mass_sub_energy_le_of_near
    (fun i => by
      have := (Finset.mem_filter.mp i.2).2.2
      show (2 : ℝ) ≤ (D.m i : ℝ); exact_mod_cast this)
    (fun p => by show (1 : ℝ) ≤ (D.m p : ℝ); exact_mod_cast D.one_le_m p)
    (fun i => norm_blockReVec_le_one D c hc
      (hPois i (hS1on i ((Finset.mem_sdiff.mp i.2).1))))
    (fun i => norm_blockReVec_le_one D c hc (hPois i (hS1on i (hM i.2))))
    σ hnear
  rw [Fintype.card_coe] at h
  exact h

end Block


end

end RHTower
