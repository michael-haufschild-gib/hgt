import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Window.Physical
import GaloisForLFunctions.HTGeometry.WeldClassTable

/-! # The composed shell clock and unique optimal heights at distinct primes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Window

open Real
open PrimeCalibration (log_pos_prime)

/-- A real channel projection is exactly an integer half-turn of the shell phase. -/
theorem real_projection (n : ℕ+) (s : ℂ) :
    (projection s n).im=0 ↔ ∃ j : ℤ, s.im*energy n=(j : ℝ)*π := by
  have hn : 0 < ((n : ℕ) : ℝ) := Nat.cast_pos.mpr n.pos
  rw [projected_heat,heat,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,add_zero,mul_eq_zero,or_iff_right (sqrt_pos.mpr hn).ne',Complex.exp_im,
    mul_eq_zero,or_iff_right (exp_pos _).ne']
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add,
    Complex.neg_im,neg_mul,sin_neg,neg_eq_zero,sin_eq_zero_iff]
  exact exists_congr fun _ => eq_comm

/-- Candidate grid heights are exactly the real phases of the composed shell. -/
theorem real_composite (p q : Nat.Primes) (s : ℂ) :
    (projection s (atom p*atom q)).im=0 ↔ ∃ j : ℤ, s.im=(j : ℝ)*spacing p q := by
  have nonzero := (add_pos (log_pos_prime p) (log_pos_prime q)).ne'
  rw [real_projection,energy_mul]
  simp only [atom,energy,label_one_quantum,spacing]
  apply exists_congr
  intro j
  rw [←mul_div_assoc,eq_div_iff nonzero]

private theorem integer_relation {p q : Nat.Primes} (pq : p≠q) (n m : ℤ)
    (eq : (n : ℝ)*share p q=(m : ℝ)) : n=0 ∧ m=0 := by
  have den := (add_pos (log_pos_prime p) (log_pos_prime q)).ne'
  unfold share at eq
  rw [←mul_div_assoc,div_eq_iff den] at eq
  have relation : ((n-m : ℤ) : ℝ)*log p.val+((-m : ℤ) : ℝ)*log q.val=0 := by
    push_cast
    linear_combination eq
  obtain ⟨h,k⟩ := _root_.GaloisForLFunctions.RHTower.two_prime_log_indep p.property q.property
    (fun h => pq (Subtype.ext h)) (n-m) (-m) relation
  omega

/-- Distinct grid indices yield distinct absolute observations. -/
theorem distinct_samples {p q : Nat.Primes} (pq : p≠q) :
    Function.Injective (sample (share p q)) := by
  intro i j h
  let α := share p q
  let u := π*(α*(i : ℝ))
  let v := π*(α*(j : ℝ))
  change |cos u|=|cos v| at h
  have sqr := congrArg (fun x : ℝ => x^2) h
  simp only [sq_abs] at sqr
  have twice : cos (2*u)=cos (2*v) := by rw [cos_two_mul,cos_two_mul,sqr]
  obtain ⟨m,hm | hm⟩ := cos_eq_cos_iff.mp twice
  · have eq : (((j : ℤ)-(i : ℤ) : ℤ) : ℝ)*α=(m : ℝ) := by
      apply mul_right_cancel₀ (show 2*π≠0 by positivity)
      dsimp only [u,v] at hm
      push_cast
      linear_combination hm
    obtain ⟨z,_⟩ := integer_relation pq _ _ eq
    omega
  · have eq : (((j : ℤ)+(i : ℤ) : ℤ) : ℝ)*α=(m : ℝ) := by
      apply mul_right_cancel₀ (show 2*π≠0 by positivity)
      dsimp only [u,v] at hm
      push_cast
      linear_combination hm
    obtain ⟨z,_⟩ := integer_relation pq _ _ eq
    omega

theorem positive_minimum {p q : Nat.Primes} (pq : p≠q) (N : ℕ) :
    0 < floorValue (share p q) N := by
  obtain ⟨j,hit⟩ := attained (share p q) N
  rw [←hit,sample,abs_pos]
  intro zero
  obtain ⟨m,eq⟩ := cos_eq_zero_iff.mp zero
  have rel : ((2*(j.val : ℤ) : ℤ) : ℝ)*share p q=((2*m+1 : ℤ) : ℝ) := by
    apply mul_right_cancel₀ pi_ne_zero
    push_cast
    linear_combination 2*eq
  have imp := (integer_relation pq _ _ rel).2
  omega

/-- The least physical reading occurs at one height, where the two
elementary phases compose to a real amplitude. -/
theorem unique_composite_minimum {p q : Nat.Primes} (pq : p≠q) (σ : ℝ) (off : σ≠1/2) (N : ℕ) :
    (∃! t : ℝ, t ∈ Set.Icc 0 ((N : ℝ)*spacing p q) ∧
      observed p q σ t=floorValue (share p q) N) ∧
    (∀ t ∈ Set.Icc 0 ((N : ℝ)*spacing p q), observed p q σ t=floorValue (share p q) N →
      (projection (⟨σ,t⟩ : ℂ) (atom p*atom q)).im=0) := by
  have loc (t : ℝ) (ht : t ∈ Set.Icc 0 ((N : ℝ)*spacing p q))
      (h : observed p q σ t=floorValue (share p q) N) :=
    (physical_minimizers p q σ t off N ht.1 ht.2).mp h
  constructor
  · obtain ⟨t,ht,he⟩ := (physical_minimum p q σ off N).1
    refine ⟨t,⟨ht,he⟩,?_⟩
    rintro v ⟨hv,ve⟩
    obtain ⟨i,hi,is⟩ := loc v hv ve
    obtain ⟨j,hj,js⟩ := loc t ht he
    rw [hi,hj,distinct_samples pq (is.trans js.symm)]
  · intro t ht h
    obtain ⟨j,hj,_⟩ := loc t ht h
    apply (real_composite p q _).mpr
    exact ⟨(j.val : ℤ),by simpa only [Int.cast_natCast] using hj⟩

#print axioms real_projection
#print axioms real_composite
#print axioms distinct_samples
#print axioms positive_minimum
#print axioms unique_composite_minimum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Window
