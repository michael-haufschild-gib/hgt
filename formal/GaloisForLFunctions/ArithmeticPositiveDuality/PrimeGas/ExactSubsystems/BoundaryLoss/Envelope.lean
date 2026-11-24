import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.ThermalReflection

/-! # The Euler lower bound for the interference of an exact finite factor -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open InverseSpectrum.ShellMixing
open _root_.RHTower.PrimeCoShift

/-- Natural prime labels of an occupation window. -/
def primeWindow (P : Finset Nat.Primes) : Finset ℕ := P.map ⟨Subtype.val,Subtype.val_injective⟩

theorem primeWindow_primes (P : Finset Nat.Primes) : ∀ p ∈ primeWindow P, p.Prime := by
  rintro _ hp
  obtain ⟨q,_,rfl⟩ := Finset.mem_map.mp hp
  exact q.property

/-- The normalized modulus of the complete Euler product on P. -/
def eulerEnvelope (P : Finset Nat.Primes) (s : ℂ) : ℝ :=
  ∏ p ∈ P, ‖1-heat (s.re : ℂ) (primePNat p)‖ / ‖1-heat s (primePNat p)‖

/-- Visibility of the finite thermal trace relative to its positive real value. -/
def traceVisibility {ι : Type*} [Fintype ι] (a : ι → ℕ+) (s : ℂ) : ℝ :=
  ‖finiteHeatTrace a s‖ / ‖finiteHeatTrace a (s.re : ℂ)‖

theorem real_heat_eq_norm (s : ℂ) (n : ℕ+) : heat (s.re : ℂ) n = (‖heat s n‖ : ℂ) := by
  rw [norm_heat,heat,Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg]

theorem prime_heat_lt_one {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) : ‖heat s (primePNat p)‖ < 1 := by
  rw [norm_heat,Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hs) (prime_energy_pos p)

/-- The complementary trace can lose visibility only through cancellation among its phases. -/
theorem window_norm_le_real {ι κ : Type*} (P : Finset Nat.Primes) {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) {s : ℂ} (hs : 0 < s.re) :
    ‖windowTrace (primeWindow P) b s‖ ≤ ‖windowTrace (primeWindow P) b (s.re : ℂ)‖ := by
  let W := primeWindow P
  have hb := (exactWindow_absolute W (primeWindow_primes P) h hs).2
  have he : windowTrace W b (s.re : ℂ) = ((∑' j : WindowState W b, ‖heat s (b j.val)‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr (fun j => real_heat_eq_norm s (b j.val))
  rw [show windowTrace (primeWindow P) b (s.re : ℂ) = _ from he,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
  exact norm_tsum_le_tsum_norm hb

private theorem norm_euler (P : Finset Nat.Primes) (s : ℂ) :
    ‖RHTower.thetaEulerStageZeta (primeWindow P) s‖ = (∏ p ∈ P, ‖1-heat s (primePNat p)‖)⁻¹ := by
  simp only [RHTower.thetaEulerStageZeta,primeWindow,Finset.prod_map,norm_prod,norm_inv,
    heat_eq_cpow,Finset.prod_inv_distrib]
  rfl

theorem euler_normalization (P : Finset Nat.Primes) (s : ℂ) :
    eulerEnvelope P s =
      ‖RHTower.thetaEulerStageZeta (primeWindow P) s‖ / ‖RHTower.thetaEulerStageZeta (primeWindow P) (s.re : ℂ)‖ := by
  rw [norm_euler,norm_euler,eulerEnvelope,Finset.prod_div_distrib,inv_div_inv]

theorem finite_window_eq {ι : Type*} [Fintype ι] {a : ι → ℕ+} {P : Finset Nat.Primes}
    (ha : ∀ i, (a i).val ∈ Nat.factoredNumbers (primeWindow P)) (s : ℂ) :
    windowTrace (primeWindow P) a s = finiteHeatTrace a s :=
  ((Equiv.subtypeUnivEquiv ha).tsum_eq (fun i => heat s (a i))).trans (tsum_fintype _)

/-- The quotient between the Euler visibility and the finite visibility is exactly the complementary visibility. -/
theorem visibility_product {ι κ : Type*} [Fintype ι] (P : Finset Nat.Primes) {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) (ha : ∀ i, (a i).val ∈ Nat.factoredNumbers (primeWindow P))
    {s : ℂ} (hs : 0 < s.re) :
    traceVisibility a s * (‖windowTrace (primeWindow P) b s‖ / ‖windowTrace (primeWindow P) b (s.re : ℂ)‖) =
      eulerEnvelope P s := by
  rw [euler_normalization P s,← exactWindow_product _ (primeWindow_primes P) h hs,
    ← exactWindow_product _ (primeWindow_primes P) h (s := (s.re : ℂ)) hs, norm_mul,norm_mul,
    finite_window_eq ha,finite_window_eq ha,traceVisibility]
  exact div_mul_div_comm _ _ _ _

theorem envelope_le_visibility {ι κ : Type*} [Fintype ι] (P : Finset Nat.Primes) {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) (ha : ∀ i, (a i).val ∈ Nat.factoredNumbers (primeWindow P))
    {s : ℂ} (hs : 0 < s.re) : eulerEnvelope P s ≤ traceVisibility a s := by
  have hb := (exactWindow_zero_free _ (primeWindow_primes P) h (s := (s.re:ℂ)) hs).2
  rw [← visibility_product P h ha hs]
  exact mul_le_of_le_one_right (div_nonneg (norm_nonneg _) (norm_nonneg _))
    ((div_le_one (norm_pos_iff.mpr hb)).mpr (window_norm_le_real P h hs))

#print axioms primeWindow_primes
#print axioms real_heat_eq_norm
#print axioms prime_heat_lt_one
#print axioms window_norm_le_real
#print axioms euler_normalization
#print axioms finite_window_eq
#print axioms visibility_product
#print axioms envelope_le_visibility

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
