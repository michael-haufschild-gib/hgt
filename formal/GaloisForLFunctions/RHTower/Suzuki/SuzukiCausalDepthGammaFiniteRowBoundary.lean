import GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalDepthGammaUnboundedSource

/-!
# Exact finite-row boundary condition for the two-leg Gamma source

A finite linear combination of the literal deattenuated Gamma rows is a Hilbert
source row exactly when its Jacobi-weighted value at the boundary is zero.
The sole obstruction is explicit; adjacent cancellation removes all other
finite-row obstructions. No source coefficient or Gram pairing is altered.
-/

open scoped BigOperators InnerProduct
set_option autoImplicit false

noncomputable section

namespace RHTower

/-- Hilbert correction of row `k` by the first row, obtained by adjacent cancellation. -/
def suzukiGammaBoundaryCorrectedRow (h a : Set.Ioi (0 : ℝ)) :
    ℕ → SuzukiCausalDepthGammaTraceL2
  | 0 => 0
  | k + 1 =>
      ((suzukiGammaBoundaryCoefficient (k + 1) : ℂ) /
          (suzukiGammaBoundaryCoefficient k : ℂ)) • suzukiGammaBoundaryCorrectedRow h a k -
        ((suzukiGammaBoundaryCoefficient 0 : ℂ) /
          (suzukiGammaBoundaryCoefficient k : ℂ)) • suzukiGammaBoundaryRowVector h a k

theorem suzukiGammaBoundaryCorrectedRow_coordinate
    (h a : Set.Ioi (0 : ℝ)) (k : ℕ) (pe : Nat.Primes × ℕ) :
    suzukiGammaBoundaryCorrectedRow h a k (Sum.inl pe) =
      (suzukiGammaBoundaryCoefficient 0 : ℂ) * suzukiGammaTwoLegColumn h a pe (Sum.inr k) -
        (suzukiGammaBoundaryCoefficient k : ℂ) * suzukiGammaTwoLegColumn h a pe (Sum.inr 0) := by
  induction k with
  | zero => simp [suzukiGammaBoundaryCorrectedRow]
  | succ k ih =>
    have hc : (suzukiGammaBoundaryCoefficient k : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (suzukiGammaBoundaryCoefficient_pos k).ne'
    have hrow : suzukiGammaBoundaryRowVector h a k (Sum.inl pe) =
        (suzukiGammaBoundaryCoefficient (k + 1) : ℂ) *
            suzukiGammaTwoLegColumn h a pe (Sum.inr k) -
          (suzukiGammaBoundaryCoefficient k : ℂ) *
            suzukiGammaTwoLegColumn h a pe (Sum.inr (k + 1)) := by
      rw [suzukiGammaTwoLegColumn_inr, suzukiGammaTwoLegColumn_inr]
      change (suzukiGammaBoundaryRow h.1 a.1 k pe : ℂ) = _
      unfold suzukiGammaBoundaryRow
      push_cast
      ring
    change ((suzukiGammaBoundaryCoefficient (k + 1) : ℂ) /
          (suzukiGammaBoundaryCoefficient k : ℂ)) *
        suzukiGammaBoundaryCorrectedRow h a k (Sum.inl pe) -
      ((suzukiGammaBoundaryCoefficient 0 : ℂ) /
          (suzukiGammaBoundaryCoefficient k : ℂ)) *
        suzukiGammaBoundaryRowVector h a k (Sum.inl pe) = _
    rw [ih, hrow]
    field_simp [hc]
    ring

/-- Exact decomposition into a Hilbert row and one boundary coefficient times the first row. -/
theorem suzukiGammaFiniteRow_boundary_decomposition
    (h a : Set.Ioi (0 : ℝ)) (s : Finset ℕ) (c : ℕ → ℂ) (pe : Nat.Primes × ℕ) :
    (∑ k ∈ s, c k • suzukiGammaBoundaryCorrectedRow h a k) (Sum.inl pe) =
      (suzukiGammaBoundaryCoefficient 0 : ℂ) *
          (∑ k ∈ s, c k * suzukiGammaTwoLegColumn h a pe (Sum.inr k)) -
        (∑ k ∈ s, c k * (suzukiGammaBoundaryCoefficient k : ℂ)) *
          suzukiGammaTwoLegColumn h a pe (Sum.inr 0) := by
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    suzukiGammaBoundaryCorrectedRow_coordinate, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem no_suzukiGammaFirstRow_hilbert_representative (h a : Set.Ioi (0 : ℝ)) :
    ¬ ∃ v : SuzukiCausalDepthGammaTraceL2, ∀ p : Nat.Primes,
      v (Sum.inl (p, 0)) = suzukiGammaTwoLegColumn h a (p, 0) (Sum.inr 0) := by
  rintro ⟨v, hv⟩
  have hi : Function.Injective (fun p : Nat.Primes =>
      (Sum.inl (p, 0) : SuzukiCausalDepthGammaTraceIndex)) := by
    intro p q hpq
    exact congrArg Prod.fst (Sum.inl.inj hpq)
  have hs := (HilbertSchmidt.summable_coe_sq v).comp_injective hi
  apply not_summable_suzukiGammaTwoLegColumn_first_norm_sq h a
  exact hs.congr fun p => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hv p)

/-- Exact domain classification for every finite Gamma test row of the actual source. -/
theorem suzukiGammaFiniteRow_hilbert_iff_boundary_zero
    (h a : Set.Ioi (0 : ℝ)) (s : Finset ℕ) (c : ℕ → ℂ) :
    (∃ v : SuzukiCausalDepthGammaTraceL2, ∀ pe : Nat.Primes × ℕ,
      v (Sum.inl pe) = ∑ k ∈ s, c k * suzukiGammaTwoLegColumn h a pe (Sum.inr k)) ↔
      ∑ k ∈ s, c k * (suzukiGammaBoundaryCoefficient k : ℂ) = 0 := by
  let W : SuzukiCausalDepthGammaTraceL2 :=
    ∑ k ∈ s, c k • suzukiGammaBoundaryCorrectedRow h a k
  let B : ℂ := ∑ k ∈ s, c k * (suzukiGammaBoundaryCoefficient k : ℂ)
  have hc : (suzukiGammaBoundaryCoefficient 0 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (suzukiGammaBoundaryCoefficient_pos 0).ne'
  have hW (pe : Nat.Primes × ℕ) : W (Sum.inl pe) =
      (suzukiGammaBoundaryCoefficient 0 : ℂ) *
        (∑ k ∈ s, c k * suzukiGammaTwoLegColumn h a pe (Sum.inr k)) -
      B * suzukiGammaTwoLegColumn h a pe (Sum.inr 0) :=
    suzukiGammaFiniteRow_boundary_decomposition h a s c pe
  constructor
  · rintro ⟨v, hv⟩
    change B = 0
    by_contra hB
    apply no_suzukiGammaFirstRow_hilbert_representative h a
    refine ⟨B⁻¹ • ((suzukiGammaBoundaryCoefficient 0 : ℂ) • v - W), fun p => ?_⟩
    change B⁻¹ * ((suzukiGammaBoundaryCoefficient 0 : ℂ) * v (Sum.inl (p, 0)) -
      W (Sum.inl (p, 0))) = _
    rw [hv, hW]
    simp [hB]
  · intro hB
    change B = 0 at hB
    refine ⟨(suzukiGammaBoundaryCoefficient 0 : ℂ)⁻¹ • W, fun pe => ?_⟩
    change (suzukiGammaBoundaryCoefficient 0 : ℂ)⁻¹ * W (Sum.inl pe) = _
    rw [hW, hB]
    simp [hc]

/-- Every polarized finite energy pairing retains the literal two-leg Gamma kernel. -/
theorem suzukiGammaTwoLeg_finite_packet_pairing
    (h a : Set.Ioi (0 : ℝ)) (s t : Finset (Nat.Primes × ℕ))
    (c d : (Nat.Primes × ℕ) → ℂ) :
    inner ℂ (∑ pe ∈ s, c pe • suzukiGammaTwoLegColumn h a pe)
        (∑ qe ∈ t, d qe • suzukiGammaTwoLegColumn h a qe) =
      ∑ pe ∈ s, ∑ qe ∈ t,
        (starRingEnd ℂ) (c pe) * d qe *
          (((pe.1 : ℝ) * (qe.1 : ℝ) *
            suzukiCausalDepthGammaSchurKernel h.1 a.1 pe qe : ℝ) : ℂ) := by
  rw [sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right,
    suzukiGammaTwoLegColumn_inner, mul_assoc, mul_left_comm]

end RHTower
