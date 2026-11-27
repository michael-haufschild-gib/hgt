import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Channel
import GaloisForLFunctions.HTGeometry.WeldClassTable

/-! # Exact isometry detection with independent elementary primes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across

open Real
open PrimeCalibration (log_pos_prime)

variable {F : Finset Nat.Primes} [Nonempty F] {J : F → Type*}
  [∀ p, Fintype (J p)] [∀ p, Nonempty (J p)]

def allBlind (k : (p : F) → J p → ℕ+) (s : ℂ) := ∀ p i, reading p.val (k p i) s=0

private theorem incompatible {p q : Nat.Primes} (hpq : p≠q) (g h : ℕ)
    (hg : 0<g) (hh : 0<h) (m n : ℤ) :
    (2*(m : ℝ)+1)*π/(2*(g : ℝ)*log p.val) ≠ (2*(n : ℝ)+1)*π/(2*(h : ℝ)*log q.val) := by
  intro eq
  have gp : (g : ℝ)≠0 := Nat.cast_ne_zero.mpr hg.ne'
  have hq : (h : ℝ)≠0 := Nat.cast_ne_zero.mpr hh.ne'
  have lp := (log_pos_prime p).ne'
  have lq := (log_pos_prime q).ne'
  have mulEq := (div_eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) gp) lp)
    (mul_ne_zero (mul_ne_zero (by norm_num) hq) lq)).mp eq
  let a : ℤ := (2*n+1)*(g : ℤ)
  let b : ℤ := -((2*m+1)*(h : ℤ))
  have cancel : ((a : ℝ)*log p.val+(b : ℝ)*log q.val)*(2*π)=0 := by
    dsimp only [a,b]
    push_cast
    linear_combination -mulEq
  have relation := (mul_eq_zero.mp cancel).resolve_right two_pi_pos.ne'
  have zero := (_root_.GaloisForLFunctions.RHTower.two_prime_log_indep p.property q.property
    (fun v => hpq (Subtype.ext v)) a b relation).1
  exact (mul_ne_zero (by omega : 2*n+1≠0) (Int.natCast_ne_zero.mpr hg.ne')) zero

omit [Nonempty F] in
/-- Two different prime logarithms forbid any shared off-line blind
height, even when each prime has its own quarter periods. -/
theorem distinct_force (k : (p : F) → J p → ℕ+) (s : ℂ) (p q : F) (hpq : p≠q) :
    allBlind k s ↔ s.re=1/2 := by
  constructor
  · intro all
    by_contra off
    obtain ⟨_,m,hm⟩ := ((blind_heights p.val (k p) s).mp (all p)).resolve_left off
    obtain ⟨_,n,hn⟩ := ((blind_heights q.val (k q) s).mp (all q)).resolve_left off
    exact incompatible (fun h => hpq (Subtype.ext h)) _ _
      (fundamental_pos (k p)) (fundamental_pos (k q)) m n (hm.symm.trans hn)
  · intro line p
    exact (blind_heights p.val (k p) s).mpr (Or.inl line)

/-- A finite detector is exact precisely when it uses distinct primes
or distinct two-adic occupation classes above one prime. -/
theorem exact_detector (k : (p : F) → J p → ℕ+) :
    (∀ s : ℂ, allBlind k s ↔ ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x) ↔
    (∃ p q : F, p≠q) ∨ ∃ (p : F) (i j : J p),
      (k p i : ℕ).factorization 2≠(k p j : ℕ).factorization 2 := by
  classical
  constructor
  · intro test
    by_cases two : ∃ p q : F, p≠q
    · exact Or.inl two
    push Not at two
    let p : F := Classical.choice inferInstance
    have single (s : ℂ) : allBlind k s ↔ ∀ i, reading p.val (k p i) s=0 := by
      refine ⟨fun h => h p,?_⟩
      intro h q
      have eq := two q p
      subst q
      exact h
    obtain ⟨i,j,hij⟩ := (uniform_isometry p.val (k p)).mp (fun s => (single s).symm.trans (test s))
    exact Or.inr ⟨p,i,j,hij⟩
  · rintro (⟨p,q,hpq⟩ | ⟨p,i,j,hij⟩) s
    · exact (distinct_force k s p q hpq).trans (split_isometric_iff s).symm
    · constructor
      · intro h
        exact ((uniform_isometry p.val (k p)).mpr ⟨i,j,hij⟩ s).mp (h p)
      · intro h q
        exact (blind_heights q.val (k q) s).mpr (Or.inl ((split_isometric_iff s).mp h))

/-- For a detecting family, RH is exactly the vanishing of its
reciprocal readings at every strip zero of the continued partition. -/
theorem rh_iff_readings (k : (p : F) → J p → ℕ+)
    (family : (∃ p q : F, p≠q) ∨ ∃ (p : F) (i j : J p),
      (k p i : ℕ).factorization 2≠(k p j : ℕ).factorization 2) :
    RiemannHypothesis ↔ ∀ s : OpenStrip, riemannZeta s.val=0 → allBlind k s.val := by
  let p : F := Classical.choice inferInstance
  have property (s : ℂ) : channelReading p.val s=0 ↔ allBlind k s :=
    (intrinsic_isometry p.val s).trans (((exact_detector k).mpr family) s).symm
  simpa only [property] using rh_iff_channel_reading p.val

#print axioms rh_iff_readings
#print axioms distinct_force
#print axioms exact_detector

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across
