import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Commensurable.AlgebraicShell

/-! # Stabilization of all normalized forced readings at one common dilation -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Finset Set

private theorem force_multiple {t u : ℝ} {a b : ℕ} (h : Forces (t*a) (u*a)) (dvd : a ∣ b) :
    Forces (t*b) (u*b) := by
  obtain ⟨k,rfl⟩ := dvd
  simpa only [Nat.cast_mul,mul_assoc] using forces_dilate h k

/-- A finite union of normalized forced sets stabilizes at a common
multiple of the witnessing integer scales, and at every multiple thereafter. -/
theorem common_scale {t : ℝ} (finite : (accumulated t).Finite) :
    ∃ M : ℕ, 0<M ∧ ∀ k : ℕ, 0<k → ∀ u : ℝ, 0<u →
      (Forces (t*↑(M*k)) (u*↑(M*k)) ↔ u ∈ accumulated t) := by
  classical
  letI : Fintype (accumulated t) := finite.fintype
  have witnesses (u : accumulated t) : ∃ m : ℕ, 0 < m ∧ Forces (t*m) (u.val*m) := u.property.2
  choose m pos hits using witnesses
  let M := ∏ u, m u
  have mp : 0<M := Finset.prod_pos (fun u _ => pos u)
  refine ⟨M,mp,fun k hk u hu => ⟨fun hit => ⟨hu,M*k,mul_pos mp hk,hit⟩,fun mem => ?_⟩⟩
  let v : accumulated t := ⟨u,mem⟩
  have dvd : m v ∣ M := Finset.dvd_prod_of_mem _ (mem_univ v)
  exact force_multiple (hits v) (dvd.trans (dvd_mul_right M k))

/-- An algebraic coordinate on a nontrivial shell forces a relation among prime coordinates. -/
theorem algebraic_shell_resonant (n : ℕ+) (hn : 1<n.val) {t : ℝ} (ht : 0<t)
    (alg : IsAlgebraic ℚ (shellPower t n)) : Resonant t := by
  by_contra no
  apply (Set.Ioi_infinite (0 : ℝ)).not_finite
  apply (accumulated_finite n hn ht alg).subset
  intro u hu
  have force := (forces_iff ht hu).mpr (Or.inl (by rw [zero_kernel no]; exact bot_le))
  exact ⟨hu,1,zero_lt_one,by simpa only [Nat.cast_one,mul_one] using force⟩

private theorem least_at_scale {t : ℝ} (ht : 0<t) (res : Resonant t) {j : ℕ} (hj : 0<j)
    (stable : ∀ u : ℝ, 0<u → (Forces (t*j) (u*j) ↔ u ∈ accumulated t)) :
    ∃ S : Set ℝ, Attainable S ∧ t*j ∈ S ∧ ∀ u : ℝ, 0<u → (u*j ∈ S ↔ u ∈ accumulated t) := by
  have hp : 0<(j : ℝ) := Nat.cast_pos.mpr hj
  have src : 0<t*j := mul_pos ht hp
  have rs : Resonant (t*j) := (resonant_nat_iff (m := j) ht hj).mpr res
  refine ⟨consequences (t*j),least_spectrum (t := t*j) src rs,⟨src,fun _ _ h => h⟩,?_⟩
  intro u hu
  exact ⟨fun hit => (stable u hu).mp hit.2,fun hit => ⟨mul_pos hu hp,(stable u hu).mpr hit⟩⟩

/-- An algebraic coordinate on just one nontrivial integer shell suffices
to realize the entire stabilized list by a least finite physical spectrum. -/
theorem stabilized_spectra (n : ℕ+) (hn : 1<n.val) {t : ℝ} (ht : 0<t)
    (alg : IsAlgebraic ℚ (shellPower t n)) :
    ∃ M : ℕ, 0<M ∧ ∀ k : ℕ, 0<k → ∃ S : Set ℝ, Attainable S ∧ t*↑(M*k) ∈ S ∧
      ∀ u : ℝ, 0<u → (u*↑(M*k) ∈ S ↔ u ∈ accumulated t) := by
  have finite := accumulated_finite n hn ht alg
  have res := algebraic_shell_resonant n hn ht alg
  obtain ⟨M,mp,stabilize⟩ := common_scale (t := t) finite
  exact ⟨M,mp,fun k hk => least_at_scale (j := M*k) ht res (mul_pos mp hk) (stabilize k hk)⟩

#print axioms algebraic_shell_resonant
#print axioms common_scale
#print axioms stabilized_spectra

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
