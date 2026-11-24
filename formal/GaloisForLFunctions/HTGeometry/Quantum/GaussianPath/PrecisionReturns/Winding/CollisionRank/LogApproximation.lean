import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Extremal

/-! # A simultaneous approximation inequality at every nonzero denominator -/

open Real Set
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.CollisionRank
noncomputable section

/-- Dilating every denominator by one fixed integer absorbs the finite
exceptional set in the definition of extremality. -/
theorem uniform_log_approximation {n : ℕ} {y : Fin n → ℝ} (hy : ¬ KleinbockMargulis.VWA y)
    {η : ℝ} (hη : 0 < η) :
    let b := ((n:ℝ))⁻¹+η
    ∃ C : ℝ, ∀ q : ℕ, 0 < q → ∀ p : Fin n → ℤ, ∀ R > (0:ℝ),
      (∀ i, |(q:ℝ)*y i-(p i:ℝ)| ≤ R) → -log R ≤ C+b*log (q:ℝ) := by
  intro b
  obtain ⟨Q,hQ⟩ := (KleinbockMargulis.finite_of_not_vwa hy hη).bddAbove
  let L := Q+1
  have hL : 0 < L := Nat.succ_pos Q
  have hL' := Nat.cast_pos (α:=ℝ).mpr hL
  refine ⟨(1+b)*log (L:ℝ),?_⟩
  intro q hq p R hR hhit
  have hq' := Nat.cast_pos (α:=ℝ).mpr hq
  have hlarge : Q < L*q := (Nat.lt_succ_self Q).trans_le (Nat.le_mul_of_pos_right L hq)
  have hstrict : ((L*q:ℕ):ℝ)^(-b) < (L:ℝ)*R := by
    by_contra! hbad
    apply hlarge.not_ge
    apply hQ
    refine ⟨Nat.mul_pos hL hq,fun i => (L:ℤ)*p i,fun i => ?_⟩
    have he : ((L*q:ℕ):ℝ)*y i-(((L:ℤ)*p i:ℤ):ℝ)=(L:ℝ)*((q:ℝ)*y i-(p i:ℝ)) := by
      push_cast; ring
    rw [he,abs_mul,abs_of_pos hL']
    rw [show -b= -(n:ℝ)⁻¹-η by dsimp only [b]; ring] at hbad
    exact (mul_le_mul_of_nonneg_left (hhit i) hL'.le).trans hbad
  rw [Nat.cast_mul] at hstrict
  have hl := log_lt_log (rpow_pos_of_pos (mul_pos hL' hq') _) hstrict
  rw [log_rpow (mul_pos hL' hq'),log_mul hL'.ne' hq'.ne',log_mul hL'.ne' hR.ne'] at hl
  linarith only [hl]

/-- Signed windings obey the same estimate after reversing all numerators. -/
theorem integer_log_approximation {n : ℕ} {y : Fin n → ℝ} (hy : ¬ KleinbockMargulis.VWA y)
    {η : ℝ} (hη : 0 < η) :
    let b := ((n:ℝ))⁻¹+η
    ∃ C : ℝ, ∀ q : ℤ, q ≠ 0 → ∀ p : Fin n → ℤ, ∀ R > (0:ℝ),
      (∀ i, |(q:ℝ)*y i-(p i:ℝ)| ≤ R) → -log R ≤ C+b*log |(q:ℝ)| := by
  intro b
  obtain ⟨C,hC⟩ := uniform_log_approximation hy hη
  refine ⟨C,?_⟩
  intro q hq p R hR hhit
  have hv : (q.natAbs:ℝ)=|(q:ℝ)| := by rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  have hn : 0 < q.natAbs := Int.natAbs_pos.mpr hq
  rw [←hv]
  rcases le_or_gt 0 (q:ℝ) with hh | hh
  · rw [abs_of_nonneg hh] at hv
    exact hC q.natAbs hn p R hR fun i => by rw [hv]; exact hhit i
  · rw [abs_of_neg hh] at hv
    apply hC q.natAbs hn (fun i => -p i) R hR
    intro i
    rw [hv,Int.cast_neg,neg_mul,neg_sub_neg,abs_sub_comm]
    exact hhit i

#print axioms integer_log_approximation
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.CollisionRank
