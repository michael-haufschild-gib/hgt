import GaloisForLFunctions.HTGeometry.PrimeLogCauchySeamRank
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Infinite quotient rank of the transported prime-log Cauchy seam

The finite-packet nonsummability theorem is promoted here to the literal quotient statement from
the paper.  Transported Cauchy sections are taken modulo the ordinary prime `ℓ²` submodule.  Every
finite family at distinct upper-half-plane nodes is linearly independent in that quotient.  Hence
the quotient contains independent families of every finite cardinality, and any linear correction
space repairing the complete family has unbounded finite rank.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Complex sequences indexed by rational primes. -/
abbrev PrimeLogSequence := Nat.Primes → ℂ

/-- The ordinary prime square-summable subspace. -/
def primeLogSquareSummable : Submodule ℂ PrimeLogSequence :=
  lpSubmodule ℂ (fun _ : Nat.Primes => ℂ) 2

/-- Prime sequences modulo the ordinary positive `ℓ²` subspace. -/
abbrev PrimeLogCauchyQuotient := PrimeLogSequence ⧸ primeLogSquareSummable

/-- A transported Cauchy section.  The square-root normalization is chosen so that its squared norm
is definitionally the packet energy used by `PrimeLogCauchySeamRank`. -/
def primeLogTransportedCauchySection (b : ℝ) (z : ℂ) : PrimeLogSequence :=
  fun p => (Real.sqrt ((p : ℝ) ^ (2 * b - 1)) : ℂ) *
    (z - (primeLogSupport p : ℂ))⁻¹

/-- A finite packet before passage to the quotient. -/
def primeLogTransportedCauchyPacket {n : ℕ}
    (z c : Fin n → ℂ) (b : ℝ) : PrimeLogSequence :=
  fun p => ∑ j, c j * primeLogTransportedCauchySection b (z j) p

/-- The transported Cauchy class modulo prime `ℓ²`. -/
def primeLogTransportedCauchyClass (b : ℝ) (z : ℂ) : PrimeLogCauchyQuotient :=
  Submodule.Quotient.mk (primeLogTransportedCauchySection b z)

/-- The packet's pointwise squared norm is exactly the analytic energy from the finite-packet
theorem. -/
theorem normSq_primeLogTransportedCauchyPacket {n : ℕ}
    (z c : Fin n → ℂ) (b : ℝ) (p : Nat.Primes) :
    Complex.normSq (primeLogTransportedCauchyPacket z c b p) =
      primeLogCauchyPacketTransportEnergy z c b p := by
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  have hpnonneg : 0 ≤ (p : ℝ) ^ (2 * b - 1) := Real.rpow_nonneg hp0 _
  have hpacket : primeLogTransportedCauchyPacket z c b p =
      (Real.sqrt ((p : ℝ) ^ (2 * b - 1)) : ℂ) *
        ∑ j, c j * (z j - (primeLogSupport p : ℂ))⁻¹ := by
    rw [primeLogTransportedCauchyPacket]
    calc
      (∑ j, c j * primeLogTransportedCauchySection b (z j) p) =
          ∑ j, (Real.sqrt ((p : ℝ) ^ (2 * b - 1)) : ℂ) *
            (c j * (z j - (primeLogSupport p : ℂ))⁻¹) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [primeLogTransportedCauchySection]
        ring
      _ = _ := (Finset.mul_sum _ _ _).symm
  rw [hpacket, Complex.normSq_mul, Complex.normSq_ofReal,
    ← pow_two, Real.sq_sqrt hpnonneg]
  rfl

/-- Membership of a finite packet in the prime `ℓ²` subspace is exactly summability of its energy. -/
theorem primeLogTransportedCauchyPacket_mem_squareSummable_iff {n : ℕ}
    (z c : Fin n → ℂ) (b : ℝ) :
    primeLogTransportedCauchyPacket z c b ∈ primeLogSquareSummable ↔
      Summable (primeLogCauchyPacketTransportEnergy z c b) := by
  rw [primeLogSquareSummable, lpSubmodule]
  change Memℓp (primeLogTransportedCauchyPacket z c b) 2 ↔ _
  rw [memℓp_gen_iff (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  apply summable_congr
  intro p
  rw [Real.rpow_two]
  exact (Complex.sq_norm _).trans
    (normSq_primeLogTransportedCauchyPacket z c b p)

/-- The quotient linear combination of the Cauchy classes is represented by the corresponding
finite packet. -/
theorem linearCombination_primeLogTransportedCauchyClass {n : ℕ}
    (z : Fin n → ℂ) (b : ℝ) (c : Fin n →₀ ℂ) :
    Finsupp.linearCombination ℂ (fun j => primeLogTransportedCauchyClass b (z j)) c =
      Submodule.Quotient.mk
        (primeLogTransportedCauchyPacket z (fun j => c j) b) := by
  rw [Finsupp.linearCombination_apply]
  calc
    c.sum (fun j a => a • primeLogTransportedCauchyClass b (z j)) =
        primeLogSquareSummable.mkQ
          (c.sum fun j a => a • primeLogTransportedCauchySection b (z j)) := by
      simp only [Finsupp.sum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul, primeLogTransportedCauchyClass, Submodule.mkQ_apply]
    _ = primeLogSquareSummable.mkQ
        (primeLogTransportedCauchyPacket z (fun j => c j) b) := by
      apply congrArg primeLogSquareSummable.mkQ
      rw [Finsupp.sum_fintype c
        (fun j a => a • primeLogTransportedCauchySection b (z j)) (by simp)]
      funext p
      simp only [primeLogTransportedCauchyPacket, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = Submodule.Quotient.mk
        (primeLogTransportedCauchyPacket z (fun j => c j) b) :=
      Submodule.mkQ_apply _ _

/-- **Finite independence modulo prime `ℓ²`.**  Every packet of distinct upper-half-plane Cauchy
sections is linearly independent in the quotient. -/
theorem primeLogTransportedCauchyClass_linearIndependent {n : ℕ}
    (z : Fin n → ℂ) (hz : Function.Injective z) (hzUpper : ∀ j, 0 < (z j).im)
    {b : ℝ} (hb : 0 < b) :
    LinearIndependent ℂ (fun j => primeLogTransportedCauchyClass b (z j)) := by
  rw [linearIndependent_iff]
  intro c hc
  rw [linearCombination_primeLogTransportedCauchyClass] at hc
  have hmem : primeLogTransportedCauchyPacket z (fun j => c j) b ∈
      primeLogSquareSummable :=
    (Submodule.Quotient.mk_eq_zero primeLogSquareSummable).mp hc
  have hsum : Summable (primeLogCauchyPacketTransportEnergy z (fun j => c j) b) :=
    (primeLogTransportedCauchyPacket_mem_squareSummable_iff z (fun j => c j) b).mp hmem
  have hczero : (fun j => c j) = 0 :=
    (summable_primeLogCauchyPacketTransportEnergy_iff z (fun j => c j) hz hzUpper hb).mp hsum
  ext j
  exact congrFun hczero j

/-- Canonical distinct nodes in the upper half-plane. -/
def primeLogCanonicalCauchyNode (j : ℕ) : ℂ := (j : ℂ) + Complex.I

theorem primeLogCanonicalCauchyNode_injective :
    Function.Injective primeLogCanonicalCauchyNode := by
  intro j k hjk
  have hre := congrArg Complex.re hjk
  simpa [primeLogCanonicalCauchyNode] using hre

theorem primeLogCanonicalCauchyNode_im_pos (j : ℕ) :
    0 < (primeLogCanonicalCauchyNode j).im := by
  simp [primeLogCanonicalCauchyNode]

/-- **Infinite quotient rank, finite-rank form.**  For every `n`, the quotient contains an explicit
linearly independent family of cardinality `n`. -/
theorem primeLogCauchyQuotient_has_independent_family (n : ℕ) {b : ℝ} (hb : 0 < b) :
    LinearIndependent ℂ
      (fun j : Fin n => primeLogTransportedCauchyClass b (primeLogCanonicalCauchyNode j)) :=
  primeLogTransportedCauchyClass_linearIndependent
    (fun j : Fin n => primeLogCanonicalCauchyNode j)
    (primeLogCanonicalCauchyNode_injective.comp Fin.val_injective)
    (fun j => primeLogCanonicalCauchyNode_im_pos j) hb

/-- The quotient has genuinely infinite algebraic dimension. -/
theorem primeLogCauchyQuotient_not_moduleFinite {b : ℝ} (hb : 0 < b) :
    ¬ Module.Finite ℂ PrimeLogCauchyQuotient := by
  intro hfinite
  letI : Module.Finite ℂ PrimeLogCauchyQuotient := hfinite
  have hle := (primeLogCauchyQuotient_has_independent_family
    (Module.finrank ℂ PrimeLogCauchyQuotient + 1) hb).fintype_card_le_finrank
  simp only [Fintype.card_fin] at hle
  omega

/-- **Positive renormalization obligation.**  If a linear correction map reaches every transported
Cauchy class, then its source contains independent families of every finite cardinality. -/
theorem primeLogCauchy_repair_has_unbounded_finite_rank
    {F : Type*} [AddCommGroup F] [Module ℂ F]
    (repair : F →ₗ[ℂ] PrimeLogCauchyQuotient)
    {b : ℝ} (hb : 0 < b)
    (hrepair : ∀ z : ℂ, 0 < z.im →
      primeLogTransportedCauchyClass b z ∈ LinearMap.range repair)
    (n : ℕ) :
    ∃ f : Fin n → F, LinearIndependent ℂ f := by
  choose f hf using fun j : Fin n =>
    hrepair (primeLogCanonicalCauchyNode j) (primeLogCanonicalCauchyNode_im_pos j)
  refine ⟨f, ?_⟩
  apply LinearIndependent.of_comp repair
  have himage : repair ∘ f =
      (fun j : Fin n => primeLogTransportedCauchyClass b (primeLogCanonicalCauchyNode j)) := by
    funext j
    exact hf j
  rw [himage]
  exact primeLogCauchyQuotient_has_independent_family n hb

/-- No finite-dimensional correction space can repair every upper-half-plane Cauchy section. -/
theorem primeLogCauchy_no_finiteDimensional_repair
    {F : Type*} [AddCommGroup F] [Module ℂ F]
    (repair : F →ₗ[ℂ] PrimeLogCauchyQuotient)
    {b : ℝ} (hb : 0 < b)
    (hrepair : ∀ z : ℂ, 0 < z.im →
      primeLogTransportedCauchyClass b z ∈ LinearMap.range repair) :
    ¬ Module.Finite ℂ F := by
  intro hfinite
  letI : Module.Finite ℂ F := hfinite
  obtain ⟨f, hf⟩ := primeLogCauchy_repair_has_unbounded_finite_rank
    repair hb hrepair (Module.finrank ℂ F + 1)
  have hle := hf.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hle
  omega

end

end GaloisForLFunctions.HTGeometry
