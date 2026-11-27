import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.RelativeCoordinates

/-! # Finiteness as exact spectral stabilization -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Set

/-- Finite accumulated readings imply resonance: otherwise even the original
scale forces the entire positive half-line. -/
theorem resonant_of_finite {t : ℝ} (ht : 0<t) (fin : (accumulated t).Finite) : Resonant t := by
  by_contra missing
  apply (Set.Ioi_infinite (0 : ℝ)).not_finite
  apply fin.subset
  intro u hu
  have force := (forces_iff ht hu).mpr (Or.inl (by rw [zero_kernel missing]; exact bot_le))
  exact ⟨hu,1,zero_lt_one,by simpa only [Nat.cast_one,mul_one] using force⟩

private theorem at_scale {t : ℝ} (ht : 0<t) (res : Resonant t) {j : ℕ} (hj : 0<j)
    (eq : ∀ u : ℝ, 0<u → (Forces (t*j) (u*j) ↔ u ∈ accumulated t)) :
    ∃ S : Set ℝ, Attainable S ∧ t*j ∈ S ∧ ∀ u : ℝ, 0<u → (u*j ∈ S ↔ u ∈ accumulated t) := by
  have jp := (Nat.cast_pos.mpr hj : 0<(j : ℝ))
  have hp := mul_pos ht jp
  have rs : Resonant (t*j) := (resonant_nat_iff ht hj).mpr res
  refine ⟨consequences (t*j),least_spectrum hp rs,⟨hp,fun _ _ h => h⟩,fun u hu => ?_⟩
  exact ⟨fun hit => (eq u hu).mp hit.2,fun h => ⟨mul_pos hu jp,(eq u hu).mpr h⟩⟩

/-- Finiteness is exactly the condition for the full set of normalized
unavoidable readings to be realized at every multiple of one scale. -/
theorem finite_iff_stabilized {t : ℝ} (ht : 0<t) :
    (accumulated t).Finite ↔ ∃ M : ℕ, 0<M ∧ ∀ k : ℕ, 0<k → ∃ S : Set ℝ,
      Attainable S ∧ t*↑(M*k) ∈ S ∧ ∀ u : ℝ, 0<u → (u*↑(M*k) ∈ S ↔ u ∈ accumulated t) := by
  constructor
  · intro fin
    obtain ⟨M,pos,stable⟩ := common_scale (t := t) fin
    exact ⟨M,pos,fun k hk => at_scale ht (resonant_of_finite ht fin) (j := M*k)
      (mul_pos pos hk) (stable k hk)⟩
  · rintro ⟨M,pos,all⟩
    obtain ⟨S,physical,_,exactly⟩ := all 1 zero_lt_one
    simp only [mul_one] at exactly
    have inj : Function.Injective (fun x : ℝ => x*(M : ℝ)) := mul_left_injective₀ (Nat.cast_pos.mpr pos).ne'
    exact ((attainable_finite physical).preimage inj.injOn).subset (fun u hu => (exactly u hu.1).mpr hu)

theorem relative_stabilization (a b : ℕ+) (gap : energy b<energy a) {t : ℝ} (ht : 0<t)
    (alg : IsAlgebraic ℚ (relativePower t a b)) : ∃ M : ℕ, 0<M ∧ ∀ k : ℕ, 0<k →
      ∃ S : Set ℝ, Attainable S ∧ t*↑(M*k) ∈ S ∧
        ∀ u : ℝ, 0<u → (u*↑(M*k) ∈ S ↔ u ∈ accumulated t) :=
  (finite_iff_stabilized ht).mp (algebraic_gap_finite a b gap ht alg)

#print axioms finite_iff_stabilized
#print axioms relative_stabilization

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
