import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Commensurable.Torsion

/-! # Finite normalized targets from one algebraic shell coordinate -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Finset Real Set MvPolynomial
open scoped Polynomial

/-- Positive target orders which an integral dilation forces after normalization. -/
def accumulated (t : ℝ) := {u : ℝ | 0<u ∧ ∃ m : ℕ, 0 < m ∧ Forces (t*m) (u*m)}

theorem accumulated_iff_rational {t u : ℝ} (ht : 0<t) (hu : 0<u) :
    u ∈ accumulated t ↔ ∃ q : ℚ, 0<q ∧ Forces ((q : ℝ)*t) ((q : ℝ)*u) := by
  rw [rational_dilation_iff ht hu]
  constructor
  · rintro ⟨_,m,hm,h⟩
    exact ⟨m,hm,(scaled_forcing_iff ht hu hm).mp h⟩
  · rintro ⟨m,hm,h⟩
    exact ⟨hu,m,hm,(scaled_forcing_iff ht hu hm).mpr h⟩

private theorem shell_modulus (n : ℕ+) (v : ℝ) (χ : Nat.Primes → ℂ) {m : ℕ} (hm : 0 < m)
    (unit : ∀ p, χ p^m=1) :
    ‖aeval (fun p => χ p*(coordinates v p : ℂ)) (atom n)‖=shellPower v n := by
  have circle (p : Nat.Primes) : ‖χ p‖=1 := by
    apply (pow_left_inj₀ (norm_nonneg _) zero_le_one hm.ne').mp
    rw [← norm_pow,unit,norm_one,one_pow]
  have pos (p : Nat.Primes) : 0<coordinates v p := rpow_pos_of_pos (Nat.cast_pos.mpr p.property.pos) v
  rw [atom,aeval_monomial,map_one,one_mul]
  have product := monomial_power (label.symm n) v
  rw [Equiv.apply_symm_apply] at product
  rw [← product]
  simp only [Finsupp.prod,norm_prod,norm_pow,norm_mul,circle,one_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (pos _)]

/-- Any polynomial for one shell yields a complex root whose modulus
determines the signed target order. -/
private theorem root_of_phase {n : ℕ+} {m : ℕ} (hm : 0 < m) {t v : ℝ} (χ : TorsionSpecialization m t v)
    (P : ℤ[X]) (hp : Polynomial.aeval (shellPower t n) P=0) :
    ∃ z : ℂ, Polynomial.aeval z P=0 ∧ ‖z‖=shellPower v n := by
  obtain ⟨phase,unit,keeps⟩ := χ
  let e := (MvPolynomial.aeval (fun p => phase p*(coordinates v p : ℂ)) : PolynomialRing →ₐ[ℤ] ℂ)
  refine ⟨e (atom n),?_,shell_modulus n v phase hm unit⟩
  rw [Polynomial.aeval_algHom_apply]
  apply keeps
  rw [← Polynomial.aeval_algHom_apply,value_atom,← shellPower_exp]
  exact hp

/-- Candidate orders are indexed by complex roots of a single shell polynomial. -/
noncomputable def rootOrders (n : ℕ+) (P : ℤ[X]) : Finset ℝ := by
  classical
  exact (P.map (algebraMap ℤ ℂ)).roots.toFinset.image (fun z => |log ‖z‖|/energy n)

theorem accumulated_subset_roots (n : ℕ+) (hn : 1<n.val) {t : ℝ} (ht : 0<t)
    (P : ℤ[X]) (ne : P ≠ 0) (root : Polynomial.aeval (shellPower t n) P=0) :
    accumulated t ⊆ (↑(rootOrders n P) : Set ℝ) := by
  classical
  rintro u ⟨hu,m,hm,force⟩
  have en : 0<energy n := log_pos (Nat.one_lt_cast.mpr hn)
  have candidate (v : ℝ) (χ : TorsionSpecialization m t v) : |v| ∈ rootOrders n P := by
    obtain ⟨z,hz,mag⟩ := root_of_phase hm χ P root
    have hit := (Polynomial.mem_roots_map_of_injective (Int.cast_injective (α := ℂ)) ne).mpr hz
    apply mem_image.mpr
    refine ⟨z,Multiset.mem_toFinset.mpr hit,?_⟩
    rw [mag,shellPower_exp,log_exp,abs_mul,abs_of_pos en,mul_div_cancel_right₀ _ en.ne']
  change u ∈ rootOrders n P
  rcases (scaled_forcing_iff ht hu hm).mp force with plus | minus
  · simpa only [abs_of_pos hu] using candidate u plus
  · simpa only [abs_neg,abs_of_pos hu] using candidate (-u) minus

theorem rootOrders_card_le (n : ℕ+) (P : ℤ[X]) : (rootOrders n P).card ≤ P.natDegree := by
  classical
  exact card_image_le.trans (Multiset.toFinset_card_le _ |>.trans (Polynomial.card_roots_map_le_natDegree P))

theorem accumulated_finite (n : ℕ+) (hn : 1<n.val) {t : ℝ} (ht : 0<t)
    (alg : IsAlgebraic ℚ (shellPower t n)) : (accumulated t).Finite := by
  obtain ⟨P,ne,root⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr alg
  exact (rootOrders n P).finite_toSet.subset (accumulated_subset_roots n hn ht P ne root)

#print axioms accumulated_subset_roots
#print axioms rootOrders_card_le
#print axioms accumulated_finite

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
