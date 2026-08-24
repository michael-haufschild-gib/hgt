import GaloisForLFunctions.HTGeometry.KernelNegativeSquareCongruence

/-!
# Finite correlation order of a negative kernel witness

A negative kernel packet has a literal order: cardinality of support of its
finitely supported coefficient vector.  This leaf identifies existence of
such a packet with one negative square, defines first failing correlation
order with `⊤` for complete positivity, and proves that nonnegative diagonal
entries exclude orders zero and one.
-/

open Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*}

/-- Kernel forms are linear in their right coefficient packet. -/
theorem kernelForm_smul_right (K : X → X → ℂ)
    (f g : X →₀ ℂ) (r : ℂ) :
    kernelForm K f (r • g) = r * kernelForm K f g := by
  rw [kernelForm, kernelForm]
  rw [Finsupp.mul_sum r f]
  apply Finsupp.sum_congr
  intro y _
  rw [Finsupp.sum_smul_index']
  · calc
      g.sum (fun x b => conj (f y) * (r • b) * K x y) =
          g.sum (fun x b => r * (conj (f y) * b * K x y)) := by
        apply Finsupp.sum_congr
        intro x _
        simp only [smul_eq_mul]
        ring
      _ = r * g.sum (fun x b => conj (f y) * b * K x y) :=
        (Finsupp.mul_sum r g).symm
  · intro x
    simp

/-- Scaling both coefficient slots multiplies the quadratic form by the
nonnegative scalar `conj r * r`. -/
theorem kernelForm_smul_self (K : X → X → ℂ)
    (f : X →₀ ℂ) (r : ℂ) :
    kernelForm K (r • f) (r • f) =
      conj r * r * kernelForm K f f := by
  rw [kernelForm_smul_left, kernelForm_smul_right]
  ring

/-- A strictly negative kernel packet supported on exactly `N` nodes. -/
def HasNegativeKernelPacketOfOrder (K : X → X → ℂ) (N : ℕ) : Prop :=
  ∃ d : X →₀ ℂ, d.support.card = N ∧ (kernelForm K d d).re < 0

/-- Existence of a strictly negative finite kernel packet of arbitrary order. -/
def HasNegativeKernelPacket (K : X → X → ℂ) : Prop :=
  ∃ N : ℕ, HasNegativeKernelPacketOfOrder K N

/-- A negative finite packet is exactly one negative square in the literal
finite-negative-dimension formalism. -/
theorem hasNegativeKernelPacket_iff_negativeDimension_one (K : X → X → ℂ) :
    HasNegativeKernelPacket K ↔ HasFiniteKernelNegativeDimension K 1 := by
  constructor
  · rintro ⟨N, d, hdcard, hdneg⟩
    let b : Fin 1 → X →₀ ℂ := fun _ => d
    refine ⟨b, ?_⟩
    intro c hc
    have hc0 : c 0 ≠ 0 := by
      intro hzero
      apply hc
      funext i
      exact Fin.eq_zero i ▸ hzero
    have hsum : ∑ i, c i • b i = c 0 • d := by
      simp [b]
    rw [hsum, kernelForm_smul_self]
    have hnorm : 0 < (conj (c 0) * c 0).re := by
      rw [mul_comm, Complex.mul_conj]
      simpa using Complex.normSq_pos.mpr hc0
    have hfactor : (conj (c 0) * c 0).im = 0 := by
      rw [mul_comm, Complex.mul_conj]
      simp
    rw [Complex.mul_re, hfactor, zero_mul, sub_zero]
    exact mul_neg_of_pos_of_neg hnorm hdneg
  · rintro ⟨d, hd⟩
    let c : Fin 1 → ℂ := fun _ => 1
    have hc : c ≠ 0 := by
      intro h
      have := congrFun h 0
      simp [c] at this
    have hneg := hd c hc
    have hsum : ∑ i, c i • d i = d 0 := by
      simp [c]
    rw [hsum] at hneg
    exact ⟨(d 0).support.card, d 0, rfl, hneg⟩

/-- Any positive finite negative dimension contains one negative square. -/
theorem hasFiniteKernelNegativeDimension_one_of_pos
    (K : X → X → ℂ) {r : ℕ} (hr : 0 < r)
    (h : HasFiniteKernelNegativeDimension K r) :
    HasFiniteKernelNegativeDimension K 1 := by
  obtain ⟨d, hd⟩ := h
  let i0 : Fin r := ⟨0, hr⟩
  let c : Fin r → ℂ := fun i => if i = i0 then 1 else 0
  have hc : c ≠ 0 := by
    intro hzero
    have hval := congrFun hzero i0
    simp [c] at hval
  have hneg := hd c hc
  have hsum : ∑ i, c i • d i = d i0 := by
    classical
    simp [c]
  rw [hsum] at hneg
  rw [← hasNegativeKernelPacket_iff_negativeDimension_one]
  exact ⟨(d i0).support.card, d i0, rfl, hneg⟩

/-- A kernel with nonnegative diagonal has no negative packet supported on
fewer than two nodes. -/
theorem two_le_order_of_negativeKernelPacket_of_diagonal_nonneg
    (K : X → X → ℂ) (hdiag : ∀ x, 0 ≤ (K x x).re)
    {N : ℕ} (hN : HasNegativeKernelPacketOfOrder K N) : 2 ≤ N := by
  obtain ⟨d, rfl, hdneg⟩ := hN
  by_contra hnot
  have hcard : d.support.card ≤ 1 := by omega
  rcases Nat.eq_zero_or_pos d.support.card with hzero | hpos
  · have hsupp : d.support = ∅ := Finset.card_eq_zero.mp hzero
    have hd : d = 0 := Finsupp.support_eq_empty.mp hsupp
    rw [hd] at hdneg
    simp [kernelForm] at hdneg
  · have hone : d.support.card = 1 := by omega
    obtain ⟨x, hsupp⟩ := Finset.card_eq_one.mp hone
    have hd : d = Finsupp.single x (d x) :=
      (Finsupp.support_eq_singleton.mp hsupp).2
    rw [hd] at hdneg
    have hform :
        kernelForm K (Finsupp.single x (d x)) (Finsupp.single x (d x)) =
          conj (d x) * (d x) * K x x := by
      calc
        kernelForm K (Finsupp.single x (d x)) (Finsupp.single x (d x)) =
            kernelForm K (d x • Finsupp.single x 1)
              (d x • Finsupp.single x 1) := by simp
        _ = conj (d x) * d x *
              kernelForm K (Finsupp.single x 1) (Finsupp.single x 1) :=
          kernelForm_smul_self K (Finsupp.single x 1) (d x)
        _ = conj (d x) * d x * K x x := by rw [kernelForm_single]
    rw [hform, Complex.mul_re] at hdneg
    have him : (conj (d x) * d x).im = 0 := by
      rw [mul_comm, Complex.mul_conj]
      simp
    rw [him, zero_mul, sub_zero] at hdneg
    have hre : 0 ≤ (conj (d x) * d x).re := by
      rw [mul_comm, Complex.mul_conj]
      exact Complex.normSq_nonneg _
    exact (not_lt_of_ge (mul_nonneg hre (hdiag x))) hdneg

/-- Least support size of a negative packet, with `⊤` when no negative packet
exists. -/
def kernelFirstFailingCorrelationOrder (K : X → X → ℂ) : WithTop ℕ := by
  classical
  exact if h : HasNegativeKernelPacket K then (Nat.find h : WithTop ℕ) else ⊤

/-- First failing correlation order is infinite exactly when no negative
finite kernel packet exists. -/
theorem kernelFirstFailingCorrelationOrder_eq_top_iff (K : X → X → ℂ) :
    kernelFirstFailingCorrelationOrder K = ⊤ ↔ ¬ HasNegativeKernelPacket K := by
  classical
  rw [kernelFirstFailingCorrelationOrder]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- A nonnegative diagonal forces first failing correlation order at least
two, including the `⊤` case. -/
theorem two_le_kernelFirstFailingCorrelationOrder_of_diagonal_nonneg
    (K : X → X → ℂ) (hdiag : ∀ x, 0 ≤ (K x x).re) :
    (2 : WithTop ℕ) ≤ kernelFirstFailingCorrelationOrder K := by
  classical
  rw [kernelFirstFailingCorrelationOrder]
  split_ifs with h
  · exact_mod_cast
      two_le_order_of_negativeKernelPacket_of_diagonal_nonneg K hdiag
        (Nat.find_spec h)
  · simp

end
end GaloisForLFunctions.HTGeometry
