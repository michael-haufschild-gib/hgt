import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ParityPairingOperator
import GaloisForLFunctions.HTGeometry.ConstitutiveMarkedSymmetryQuotient

/-!
# Prime interference forces the relative grading

A pair of multiplicative shell phases anticommutes with the parity pairing
exactly when the two paths interfere destructively on every prime shell.
On the kernel only the square of their common phase survives.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open ContinuousLinearMap GaloisForLFunctions.HTGeometry

private theorem prime_not_square_state (p : Nat.Primes) :
    ((p : ℕ+), (1 : ℕ+)) ∉ Set.range squareState := by
  rintro ⟨n,h⟩
  exact p.property.ne_one (congrArg (fun x : ℕ+ × ℕ+ => (x.1 : ℕ)) h.symm)

theorem parityPartner_prime (p : Nat.Primes) : parityPartner ((p : ℕ+),1) = (1,(p : ℕ+)) := by
  let y := parityPartner ((p : ℕ+),1)
  have hm : y.1*y.2 = (p : ℕ+) := (parityPartner_product ((p : ℕ+),1)).trans (mul_one _)
  have hd : (y.1 : ℕ) ∣ (p : ℕ) := ⟨(y.2 : ℕ),congrArg PNat.val hm.symm⟩
  rcases (Nat.dvd_prime p.property).mp hd with h1 | hprime
  · have ha : y.1 = 1 := PNat.coe_injective h1
    exact Prod.ext ha (by simpa only [ha,one_mul] using hm)
  · have ha : y.1 = (p : ℕ+) := PNat.coe_injective hprime
    have hb : y.2 = 1 := mul_left_cancel (a := (p : ℕ+)) (by simpa only [ha,mul_one] using hm)
    exact (prime_not_square_state p ((parityPartner_fixed_iff _).mp (Prod.ext ha hb))).elim

/-- Exactly the Liouville-relative phases cancel in every elementary two-copy shell. -/
theorem prime_interference_iff (χ ψ : ℕ+ →* Circle) :
    (∀ p : Nat.Primes, (χ (p : ℕ+) : ℂ) + (ψ (p : ℕ+) : ℂ) = 0) ↔ ψ = χ * primeParity := by
  constructor
  · intro h
    apply prime_phase_coordinates.injective
    funext p
    apply Circle.coe_injective
    change (ψ (p : ℕ+) : ℂ) = ((χ (p : ℕ+) * primeParity (p : ℕ+) : Circle) : ℂ)
    rw [primeParity_prime, Circle.coe_mul, Circle.coe_neg, Circle.coe_one, mul_neg_one]
    linear_combination h p
  · rintro rfl p
    simp only [MonoidHom.mul_apply, primeParity_prime, Circle.coe_neg, mul_neg_one, add_neg_cancel]

/-- Diagonal insertion of independent phases on the two copies. -/
def twoCopyPhase (χ ψ : ℕ+ →* Circle) : PairGas →L[ℂ] PairGas :=
  lpDiagonalCLM (fun x : ℕ+ × ℕ+ => ((χ x.1 : ℂ) * (ψ x.2 : ℂ))) zero_le_one
    (fun x => by simp only [norm_mul, Circle.norm_coe, one_mul, le_refl])

private theorem relative_phase (χ : ℕ+ →* Circle) (x : ℕ+ × ℕ+) :
    (χ x.1 : ℂ) * ((χ*primeParity) x.2 : ℂ) = (χ (x.1*x.2) : ℂ) * (primeParity x.2 : ℂ) := by
  rw [MonoidHom.mul_apply, map_mul, Circle.coe_mul, Circle.coe_mul, mul_assoc]

theorem twoCopyPhase_anticommutes_iff (χ ψ : ℕ+ →* Circle) :
    parityPairing ∘L twoCopyPhase χ ψ = -(twoCopyPhase χ ψ ∘L parityPairing) ↔ ψ = χ * primeParity := by
  constructor
  · intro he
    apply (prime_interference_iff χ ψ).mp
    intro p
    let x : ℕ+ × ℕ+ := ((p : ℕ+),1)
    let y : ℕ+ × ℕ+ := (1,(p : ℕ+))
    let f : PairGas := lp.single 2 y 1
    have hv := congrArg (fun A : PairGas →L[ℂ] PairGas => A f x) he
    change parityPairing (twoCopyPhase χ ψ f) x = -((χ x.1 : ℂ) * (ψ x.2 : ℂ) * parityPairing f x) at hv
    rw [parityPairing_apply, if_neg (prime_not_square_state p), parityPairing_apply,
      if_neg (prime_not_square_state p), parityPartner_prime] at hv
    change (χ 1 : ℂ) * (ψ (p : ℕ+) : ℂ) * f y = -((χ (p : ℕ+) : ℂ) * (ψ 1 : ℂ) * f y) at hv
    have hf : f y = 1 := lp.single_apply_self 2 y 1
    simp only [hf, map_one, Circle.coe_one, mul_one, one_mul] at hv
    rw [hv, add_neg_cancel]
  · rintro rfl
    ext f x
    change parityPairing (twoCopyPhase χ (χ*primeParity) f) x =
      -((χ x.1 : ℂ) * ((χ*primeParity) x.2 : ℂ) * parityPairing f x)
    by_cases h : x ∈ Set.range squareState
    · simp only [parityPairing_apply, if_pos h, mul_zero, neg_zero]
    · have hs := parityPartner_sign x (mt (parityPartner_fixed_iff x).mp h)
      simp only [parityPairing_apply, if_neg h, twoCopyPhase, lpDiagonalCLM_apply,
        relative_phase, parityPartner_product, hs, Circle.coe_neg, mul_neg, neg_mul]

/-- The surviving square state carries only the doubled common phase. -/
theorem twoCopyPhase_square (χ : ℕ+ →* Circle) (f : PairGas) (n : ℕ+) :
    twoCopyPhase χ (χ*primeParity) f (squareState n) = (χ n : ℂ)^2 * f (squareState n) := by
  have hs : primeParity (n*n) = 1 := by
    change (-1 : Circle)^ArithmeticFunction.cardFactors ((n*n : ℕ+) : ℕ) = 1
    rw [PNat.mul_coe, ArithmeticFunction.cardFactors_mul n.ne_zero n.ne_zero, ← two_mul, pow_mul]
    simp
  change (χ 1 : ℂ) * ((χ*primeParity) (n*n) : ℂ) * f (squareState n) = _
  rw [map_one, Circle.coe_one, one_mul, MonoidHom.mul_apply, hs, mul_one, map_mul, Circle.coe_mul, sq]

theorem square_phases_trivial_iff (χ : ℕ+ →* Circle) :
    (∀ (f : parityPairing.ker) (n : ℕ+), twoCopyPhase χ (χ*primeParity) f (squareState n) =
      (f : PairGas) (squareState n)) ↔ χ^2 = 1 := by
  constructor
  · intro h
    apply MonoidHom.ext
    intro n
    apply Circle.coe_injective
    let f : Gas := lp.single 2 n 1
    have hn := h (squareKernelEquiv f) n
    rw [twoCopyPhase_square, squareKernelEquiv_coordinate] at hn
    have hf : f n = 1 := lp.single_apply_self 2 n 1
    simpa only [MonoidHom.pow_apply, Circle.coe_pow, MonoidHom.one_apply, Circle.coe_one, hf, mul_one] using hn
  · intro h f n
    have hn := congrArg (fun κ : ℕ+ →* Circle => (κ n : ℂ)) h
    simp only [MonoidHom.pow_apply, Circle.coe_pow, MonoidHom.one_apply, Circle.coe_one] at hn
    rw [twoCopyPhase_square, hn, one_mul]

/-- Independent square roots at the primes realize every target phase. -/
theorem square_phase_surjective : Function.Surjective (fun χ : ℕ+ →* Circle => χ^2) := by
  intro ρ
  choose ω hω using fun p : Nat.Primes => sq_surjective_circle (ρ (p : ℕ+))
  obtain ⟨χ,hχ⟩ := prime_phase_coordinates.surjective ω
  refine ⟨χ, prime_phase_coordinates.injective ?_⟩
  funext p
  change (χ (p : ℕ+))^2 = ρ (p : ℕ+)
  exact (congrArg (fun z : Circle => z^2) (congrFun hχ p)).trans (hω p)

/-- Anticommutation leaves complete freedom in the measured multiplicative phase on the kernel. -/
theorem every_kernel_phase_realized (ρ : ℕ+ →* Circle) :
    ∃ χ ψ : ℕ+ →* Circle,
      parityPairing ∘L twoCopyPhase χ ψ = -(twoCopyPhase χ ψ ∘L parityPairing) ∧
      ∀ (f : parityPairing.ker) (n : ℕ+), twoCopyPhase χ ψ f (squareState n) =
        (ρ n : ℂ) * (f : PairGas) (squareState n) := by
  obtain ⟨χ,hχ⟩ := square_phase_surjective ρ
  refine ⟨χ,χ*primeParity,(twoCopyPhase_anticommutes_iff _ _).mpr rfl,?_⟩
  intro f n
  have h := congrArg (fun κ : ℕ+ →* Circle => (κ n : ℂ)) hχ
  change (((χ n)^2 : Circle) : ℂ) = (ρ n : ℂ) at h
  rw [Circle.coe_pow] at h
  rw [twoCopyPhase_square,h]

theorem square_phase_fiber_iff (χ ψ : ℕ+ →* Circle) :
    χ^2 = ψ^2 ↔ (χ/ψ)^2 = 1 := by rw [div_pow,div_eq_one]

theorem squarePhase_summable_iff (χ : ℕ+ →* Circle) (s : ℂ) :
    (Summable fun n : ℕ+ => ‖(χ n : ℂ)^2 * heat s ((squareState n).1*(squareState n).2)‖) ↔
      1/2 < s.re := by
  simp only [norm_mul, norm_pow, Circle.norm_coe, one_pow, one_mul, squareKernel_summable_iff]

#print axioms squarePhase_summable_iff
#print axioms prime_interference_iff
#print axioms twoCopyPhase_anticommutes_iff
#print axioms twoCopyPhase_square
#print axioms square_phases_trivial_iff
#print axioms every_kernel_phase_realized
#print axioms square_phase_fiber_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
