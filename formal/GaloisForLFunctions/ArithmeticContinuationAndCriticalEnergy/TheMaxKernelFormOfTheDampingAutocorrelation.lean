import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheSignedWorkIsTheTangentAutocorrelation

/-!
# The max-kernel form of the damping autocorrelation

The autocorrelation of the damped Chebyshev tangent is a sum over observation horizons.  Summing
the pronic weight first turns it into a sum over *pairs of prime powers*, which is the coordinate
system the incidence and Gram programmes work in.  For arbitrary coefficient rows the exchange is
exact:

`Σ_{n ≤ T} (Σ_{j ≤ n} a_j)(Σ_{k ≤ n} b_k)/(n(n+1))
   = Σ_{j,k ≤ T} a_j b_k / max(j,k) − (Σ_{j ≤ T} a_j)(Σ_{k ≤ T} b_k)/(T+1)`,

because the pronic weight telescopes: `Σ_{max(j,k) ≤ n ≤ T} 1/(n(n+1)) = 1/max(j,k) − 1/(T+1)`.
The kernel `1/max(j,k)` is the Nyman–Beurling kernel `min(1/j, 1/k)`, and the identity proves at
once that it is positive semidefinite on `[1, T]`, with the exact formula

`Σ_{j,k ≤ T} a_j a_k / max(j,k) = Σ_{n ≤ T} (Σ_{j ≤ n} a_j)²/(n(n+1)) + (Σ_{j ≤ T} a_j)²/(T+1)`.

Specialised to the arithmetic family, with the increment `Λ_η(j) − m(η)` of the centred damped
Chebyshev function, this puts the obstruction of the continuation layer in prime-pair coordinates:

`K_T(η, ε) = Σ_{j,k ≤ T} (Λ_η(j) − m(η))(Λ_ε(k) − m(ε)) / max(j,k) − E_η(T) E_ε(T)/(T+1)`.

So the sign whose failure obstructs backward continuation is the sign of one Vasyunin-type
bilinear form in the damped von Mangoldt weights at two dampings, against one explicit horizon
boundary term.  Combined with the sign criterion, a lower bound on that bilinear form — and not on
any norm — proves the Riemann hypothesis
(`riemannHypothesis_of_maxKernelForm_ge_boundary`).
-/

open Finset RHTower GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The pronic weight telescopes -/

/-- The pronic mass of a tail of horizons: `Σ_{N ≤ n ≤ T} 1/(n(n+1)) = 1/N − 1/(T+1)`. -/
theorem sum_Icc_pronic_tail_mass {N T : ℕ} (hN : 1 ≤ N) (hNT : N ≤ T + 1) :
    ∑ n ∈ Icc N T, 1 / ((n : ℝ) * ((n : ℝ) + 1)) = 1 / (N : ℝ) - 1 / ((T : ℝ) + 1) := by
  have h1 : Ioc 0 T = Icc 1 T := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  have h2 : Ioc 0 (N - 1) = Icc 1 (N - 1) := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  have h3 : Ioc (N - 1) T = Icc N T := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  have hsplit := Finset.sum_Ioc_consecutive (f := fun n : ℕ => 1 / ((n : ℝ) * ((n : ℝ) + 1)))
    (Nat.zero_le (N - 1)) (show N - 1 ≤ T by omega)
  rw [h1, h2, h3, sum_Icc_pronic_mass, sum_Icc_pronic_mass] at hsplit
  have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
    have h := Nat.cast_sub (R := ℝ) hN
    rw [h]
    push_cast
    ring
  rw [hcast] at hsplit
  linarith

/-! ## §2. The exact exchange identity for arbitrary rows -/

/-- **The max-kernel exchange.**  Summing the pronic weight before the coefficients turns the
pronic pairing of two prefixes into a bilinear form in the Nyman–Beurling kernel `1/max(j,k)`,
with one exact horizon boundary term. -/
theorem pronicPairing_prefix_eq_maxKernel (T : ℕ) (a b : ℕ → ℝ) :
    pronicPairing T (fun n => ∑ j ∈ Icc 1 n, a j) (fun n => ∑ k ∈ Icc 1 n, b k) =
      (∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T, a j * b k / ((max j k : ℕ) : ℝ)) -
        (∑ j ∈ Icc 1 T, a j) * (∑ k ∈ Icc 1 T, b k) / ((T : ℝ) + 1) := by
  have hcut : ∀ (c : ℕ → ℝ) {n : ℕ}, n ≤ T →
      (∑ j ∈ Icc 1 n, c j) = ∑ j ∈ Icc 1 T, if j ≤ n then c j else 0 := by
    intro c n hn
    rw [← Finset.sum_filter]
    refine (Finset.sum_congr ?_ fun _ _ => rfl).symm
    ext j
    simp only [mem_filter, mem_Icc]
    omega
  have hterm : ∀ n ∈ Icc 1 T,
      (∑ j ∈ Icc 1 n, a j) * (∑ k ∈ Icc 1 n, b k) / ((n : ℝ) * ((n : ℝ) + 1)) =
        ∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T,
          (if j ≤ n then a j else 0) * (if k ≤ n then b k else 0) /
            ((n : ℝ) * ((n : ℝ) + 1)) := by
    intro n hn
    rw [hcut a (mem_Icc.mp hn).2, hcut b (mem_Icc.mp hn).2, Finset.sum_mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_div]
  have hinner : ∀ j ∈ Icc 1 T, ∀ k ∈ Icc 1 T,
      (∑ n ∈ Icc 1 T, (if j ≤ n then a j else 0) * (if k ≤ n then b k else 0) /
        ((n : ℝ) * ((n : ℝ) + 1))) =
        a j * b k / ((max j k : ℕ) : ℝ) - a j * b k / ((T : ℝ) + 1) := by
    intro j hj k hk
    have hj1 := mem_Icc.mp hj
    have hk1 := mem_Icc.mp hk
    have hsub : Icc (max j k) T ⊆ Icc 1 T := by
      intro n hn
      rw [mem_Icc] at hn ⊢
      exact ⟨le_trans (le_max_of_le_left hj1.1) hn.1, hn.2⟩
    have hzero : ∀ n ∈ Icc 1 T, n ∉ Icc (max j k) T →
        (if j ≤ n then a j else 0) * (if k ≤ n then b k else 0) /
          ((n : ℝ) * ((n : ℝ) + 1)) = 0 := by
      intro n hn hns
      rw [mem_Icc] at hn
      rw [mem_Icc, not_and] at hns
      have hlt : ¬ (max j k ≤ n) := fun h => hns h hn.2
      rw [max_le_iff, not_and_or] at hlt
      rcases hlt with h | h
      · rw [if_neg h]; ring
      · rw [if_neg h, mul_zero, zero_div]
    rw [← Finset.sum_subset hsub hzero]
    have hval : ∀ n ∈ Icc (max j k) T,
        (if j ≤ n then a j else 0) * (if k ≤ n then b k else 0) /
          ((n : ℝ) * ((n : ℝ) + 1)) = a j * b k * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
      intro n hn
      rw [mem_Icc] at hn
      rw [if_pos (le_trans (le_max_left j k) hn.1), if_pos (le_trans (le_max_right j k) hn.1)]
      ring
    rw [Finset.sum_congr rfl hval, ← Finset.mul_sum,
      sum_Icc_pronic_tail_mass (le_max_of_le_left hj1.1)
        ((max_le hj1.2 hk1.2).trans (Nat.le_succ T))]
    ring
  rw [pronicPairing, Finset.sum_congr rfl hterm, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_comm]
  rw [Finset.sum_congr rfl fun j hj =>
    Finset.sum_congr rfl fun k hk => hinner j hj k hk]
  have hprod : (∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T, a j * b k / ((T : ℝ) + 1)) =
      (∑ j ∈ Icc 1 T, a j) * (∑ k ∈ Icc 1 T, b k) / ((T : ℝ) + 1) := by
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_div]
  have hsplit : (∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T,
        (a j * b k / ((max j k : ℕ) : ℝ) - a j * b k / ((T : ℝ) + 1))) =
      (∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T, a j * b k / ((max j k : ℕ) : ℝ)) -
        ∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T, a j * b k / ((T : ℝ) + 1) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_sub_distrib]
  rw [hsplit, hprod]

/-- **The Nyman–Beurling kernel is positive semidefinite, with an exact formula.**  Its quadratic
form is the pronic energy of the prefixes plus the squared total at the horizon. -/
theorem maxKernel_quadForm_eq (T : ℕ) (a : ℕ → ℝ) :
    (∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T, a j * a k / ((max j k : ℕ) : ℝ)) =
      (∑ n ∈ Icc 1 T, (∑ j ∈ Icc 1 n, a j) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) +
        (∑ j ∈ Icc 1 T, a j) ^ 2 / ((T : ℝ) + 1) := by
  have h := pronicPairing_prefix_eq_maxKernel T a a
  rw [pronicPairing] at h
  have hsq : ∀ n ∈ Icc 1 T,
      (∑ j ∈ Icc 1 n, a j) * (∑ k ∈ Icc 1 n, a k) / ((n : ℝ) * ((n : ℝ) + 1)) =
        (∑ j ∈ Icc 1 n, a j) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
    fun n _ => by rw [← sq]
  rw [Finset.sum_congr rfl hsq] at h
  rw [← sq] at h
  linarith

theorem maxKernel_quadForm_nonneg (T : ℕ) (a : ℕ → ℝ) :
    0 ≤ ∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T, a j * a k / ((max j k : ℕ) : ℝ) := by
  rw [maxKernel_quadForm_eq]
  have h1 : 0 ≤ ∑ n ∈ Icc 1 T, (∑ j ∈ Icc 1 n, a j) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
    Finset.sum_nonneg fun n hn => by
      have : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by
        have := (mem_Icc.mp hn).1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast this
        positivity
      positivity
  have h2 : 0 ≤ (∑ j ∈ Icc 1 T, a j) ^ 2 / ((T : ℝ) + 1) := by positivity
  linarith

/-! ## §3. The arithmetic specialisation -/

/-- The increment of the centred damped Chebyshev function: `Λ_η(j) − m(η)`. -/
def dampedChebyshevIncrement (η : ℝ) (j : ℕ) : ℝ := dampedVonMangoldt η j - dampedReadout η

/-- The centred damped Chebyshev function is the prefix of its increments: the pole subtraction is
distributed one unit per horizon cell. -/
theorem dampedChebyshevError_eq_sum_increment (η : ℝ) (n : ℕ) :
    dampedChebyshevError η n = ∑ j ∈ Icc 1 n, dampedChebyshevIncrement η j := by
  unfold dampedChebyshevError dampedChebyshevIncrement
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc]
  simp [mul_comm]

/-- **The damping autocorrelation in prime-pair coordinates.**  The obstruction of the
continuation layer is one Vasyunin-type bilinear form in the damped von Mangoldt weights at two
dampings, against one explicit horizon boundary term. -/
theorem tangentCorrelation_eq_maxKernel (T : ℕ) (η ε : ℝ) :
    tangentCorrelation T η ε =
      (∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T, dampedChebyshevIncrement η j *
        dampedChebyshevIncrement ε k / ((max j k : ℕ) : ℝ)) -
        dampedChebyshevError η T * dampedChebyshevError ε T / ((T : ℝ) + 1) := by
  have h := pronicPairing_prefix_eq_maxKernel T (dampedChebyshevIncrement η)
    (dampedChebyshevIncrement ε)
  rw [tangentCorrelation]
  have hfun : ∀ θ : ℝ, (fun n => ∑ j ∈ Icc 1 n, dampedChebyshevIncrement θ j) =
      dampedChebyshevError θ :=
    fun θ => funext fun n => (dampedChebyshevError_eq_sum_increment θ n).symm
  rw [hfun, hfun] at h
  rw [h, ← dampedChebyshevError_eq_sum_increment, ← dampedChebyshevError_eq_sum_increment]

/-- **A lower bound on the prime-pair form is a continuation budget.**  If the Vasyunin-type
bilinear form of the damped von Mangoldt increments at two dampings dominates its horizon boundary
term, the damping autocorrelation is nonnegative and the Riemann hypothesis follows: no norm is
estimated anywhere. -/
theorem riemannHypothesis_of_maxKernelForm_ge_boundary
    (h : ∀ (T : ℕ) (η ε : ℝ), 0 < η → η ≤ ε → ε ≤ 1 / 2 →
      dampedChebyshevError η T * dampedChebyshevError ε T / ((T : ℝ) + 1) ≤
        ∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T, dampedChebyshevIncrement η j *
          dampedChebyshevIncrement ε k / ((max j k : ℕ) : ℝ)) :
    RiemannHypothesis :=
  riemannHypothesis_of_nonneg_tangentCorrelation fun T η ε hη hηε hε => by
    rw [tangentCorrelation_eq_maxKernel]
    linarith [h T η ε hη hηε hε]

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
