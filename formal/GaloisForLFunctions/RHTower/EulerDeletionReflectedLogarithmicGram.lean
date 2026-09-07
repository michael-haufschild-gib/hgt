import GaloisForLFunctions.RHTower.EulerDeletionCurvatureCriticalBoundary
import GaloisForLFunctions.RHTower.EulerDeletionCoprimeCrossCompletion
import GaloisForLFunctions.RHTower.EulerDeletionWeightedFifthCirculation
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianZetaGeometry
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Reflected deletion pairing: exact logarithmic boundary

The actual reflected bracket is a harmonic arithmetic Gram sum. Its gcd residue
and complete logarithmic finite part survive chronological zero landing.
-/

open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionReflectedGram
open DeletionCriticalCurvature
noncomputable section

/-- Critical-line reflection, retaining the imaginary part of the parameter. -/
def partner (s : ℂ) : ℂ := 1-star s

/-- Full real harmonic bracket of two literal positive moduli. -/
def gramPrefix (p q N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (blockDeletionCoefficient p n : ℝ)*
    (blockDeletionCoefficient q n : ℝ)/(n:ℝ)

/-- Coefficient of the logarithmic divergence, including shared arithmetic factors. -/
def residue (p q : ℕ) : ℝ := (Nat.gcd p q:ℝ)-1

/-- Complete harmonic finite part, with the overlap modulus retained. -/
def finitePart (p q : ℕ) : ℝ :=
  Real.log p+Real.log q-(Nat.gcd p q:ℝ)*Real.log (Nat.lcm p q)

/-- Literal coefficient identity before any summation or limit. -/
theorem coefficient_product (p q n : ℕ) :
    (blockDeletionCoefficient p n : ℝ)*(blockDeletionCoefficient q n : ℝ) =
      residue p q+(blockDeletionCoefficient p n:ℝ)+(blockDeletionCoefficient q n:ℝ)-
        (Nat.gcd p q:ℝ)*(blockDeletionCoefficient (Nat.lcm p q) n:ℝ) := by
  have h : (Nat.gcd p q:ℝ)*(Nat.lcm p q:ℝ) = (p:ℝ)*(q:ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm p q
  by_cases hp : p ∣ n <;> by_cases hq : q ∣ n <;>
    simp [blockDeletionCoefficient, residue, Nat.lcm_dvd_iff, hp, hq] <;> nlinarith

private theorem harmonic_Icc (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ)) = (harmonic N:ℝ) := by
  rw [sum_Icc_eq_sum_range_succ]
  simp [harmonic, div_eq_mul_inv]

/-- Exact finite logarithmic decomposition at every ordinary cutoff. -/
theorem gramPrefix_decomposition (p q N : ℕ) :
    gramPrefix p q N = residue p q*(harmonic N:ℝ)+harmonicPrefix p N+
      harmonicPrefix q N-(Nat.gcd p q:ℝ)*harmonicPrefix (Nat.lcm p q) N := by
  simp only [gramPrefix, coefficient_product, add_div, sub_div,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, harmonicPrefix]
  rw [show (∑ n ∈ Finset.Icc 1 N, residue p q/(n:ℝ)) =
      residue p q*(harmonic N:ℝ) by
        rw [← harmonic_Icc, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The full finite part follows from ordinary harmonic deletion limits. -/
theorem gramPrefix_sub_harmonic_tendsto {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    Tendsto (fun N => gramPrefix p q N-residue p q*(harmonic N:ℝ)) atTop
      (nhds (finitePart p q)) := by
  have ht := ((tendsto_harmonicPrefix hp).add (tendsto_harmonicPrefix hq)).sub
    ((tendsto_harmonicPrefix (Nat.lcm_pos hp hq)).const_mul (Nat.gcd p q:ℝ))
  change Tendsto _ atTop (nhds (Real.log p+Real.log q-
    (Nat.gcd p q:ℝ)*Real.log (Nat.lcm p q)))
  convert ht using 1
  funext N
  rw [gramPrefix_decomposition]
  ring

/-- Coprime channels have neither harmonic residue nor finite boundary. -/
theorem coprime_boundary {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : p.Coprime q) :
    residue p q = 0 ∧ finitePart p q = 0 := by
  constructor
  · simp [residue, hpq.gcd_eq_one]
  · rw [finitePart, hpq.gcd_eq_one, hpq.lcm_eq_mul, Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast hq.ne')]
    norm_num

/-- The diagonal retains its exact nontrivial logarithmic mass and finite correction. -/
theorem diagonal_boundary (p : ℕ) :
    residue p p = (p:ℝ)-1 ∧ finitePart p p = (2-(p:ℝ))*Real.log p := by
  simp only [residue, finitePart, Nat.gcd_self, Nat.lcm_self]
  constructor
  · trivial
  · ring

/-- The finite part alone already fails positivity on the actual modulus-three diagonal. -/
theorem finitePart_three_neg : finitePart 3 3 < 0 := by
  rw [(diagonal_boundary 3).2]
  norm_num
  exact Real.log_pos (by norm_num)

/-- Subtracting the logarithmic residue yields an indefinite form, even on moduli two and four. -/
theorem finitePart_two_four_indefinite :
    0 < 9*finitePart 2 2-3*finitePart 2 4-3*finitePart 4 2+finitePart 4 4 ∧
      finitePart 4 4 < 0 := by
  have hlog : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2*2 by ring, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  norm_num [finitePart, hlog]
  constructor <;> linarith

/-- Positive bases conjugate their exponent without changing logarithm branch. -/
private theorem star_weight (s : ℂ) (n : ℕ) :
    star (((n:ℂ))^(-s)) = (n:ℂ)^(-star s) := by
  have h := (Complex.cpow_conj (n:ℂ) (-s)
    (by simpa only [Complex.natCast_arg] using Real.pi_pos.ne)).symm
  simpa only [Complex.star_def, map_natCast, map_neg] using h

/-- Reflection removes the parameter from the actual diagonal pairing pointwise. -/
theorem reflected_jump_pair (p q n : ℕ) (s : ℂ) :
    eulerDeletionWeightedJump p s n * star (eulerDeletionWeightedJump q (partner s) n) =
      (((blockDeletionCoefficient (p+1) (n+1):ℝ)*
        (blockDeletionCoefficient (q+1) (n+1):ℝ)/(n+1:ℕ):ℝ):ℂ) := by
  have hn : ((n+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [eulerDeletionWeightedJump, eulerDeletionDirichletCoefficient,
    ← Nat.cast_add_one, Complex.ofReal_natCast]
  rw [star_mul', star_weight]
  have hc : star ((blockDeletionCoefficient (q+1) (n+1):ℂ)) =
      (blockDeletionCoefficient (q+1) (n+1):ℂ) := by simp
  rw [hc]
  have he : -s + -star (partner s) = (-1:ℂ) := by
    simp only [partner, star_sub, star_one, star_star]
    ring
  calc
    _ = ((blockDeletionCoefficient (p+1) (n+1):ℂ)*
      (blockDeletionCoefficient (q+1) (n+1):ℂ))*
      ((((n+1:ℕ):ℂ)^(-s))*(((n+1:ℕ):ℂ)^(-star (partner s)))) := by ring
    _ = _ := by
      rw [← Complex.cpow_add _ _ hn, he, Complex.cpow_neg_one]
      push_cast
      ring

/-- The full reflected quasi-shuffle bracket is exactly the real arithmetic Gram prefix. -/
theorem reflected_bracket_eq (p q N : ℕ) (s : ℂ) :
    crossBracketPrefix (eulerDeletionWeightedJump p s)
      (eulerDeletionWeightedJump q (partner s)) N = (gramPrefix (p+1) (q+1) N:ℂ) := by
  simp only [crossBracketPrefix, reflected_jump_pair, gramPrefix,
    sum_Icc_eq_sum_range_succ, Complex.ofReal_sum]

/-- Exact source chronology keeps the whole diagonal before any zero condition. -/
theorem reflected_chronological_decomposition (p q N : ℕ) (s : ℂ) :
    chronologicalCrossPrefix (eulerDeletionWeightedJump p s)
        (eulerDeletionWeightedJump q (partner s)) N +
      star (chronologicalCrossPrefix (eulerDeletionWeightedJump q (partner s))
        (eulerDeletionWeightedJump p s) N) +
      (residue (p+1) (q+1)*(harmonic N:ℝ):ℂ) =
      (∑ n ∈ Finset.range N, eulerDeletionWeightedJump p s n)*
        star (∑ n ∈ Finset.range N, eulerDeletionWeightedJump q (partner s) n) -
      ((harmonicPrefix (p+1) N+harmonicPrefix (q+1) N-
        (Nat.gcd (p+1) (q+1):ℝ)*harmonicPrefix (Nat.lcm (p+1) (q+1)) N):ℂ) := by
  have h := endpoint_mul_star_endpoint_eq_cross_add_reverse_add_bracket
    (eulerDeletionWeightedJump p s) (eulerDeletionWeightedJump q (partner s)) N
  rw [reflected_bracket_eq, gramPrefix_decomposition] at h
  push_cast at h ⊢
  linear_combination -h


/-- Full finite Gram positivity survives arbitrary real combinations of the channels. -/
theorem gram_quadratic_eq (S : Finset ℕ) (c : ℕ → ℝ) (N : ℕ) :
    (∑ p ∈ S, ∑ q ∈ S, c p*c q*gramPrefix p q N) =
      ∑ n ∈ Finset.Icc 1 N,
        (∑ p ∈ S, c p*(blockDeletionCoefficient p n:ℝ))^2/(n:ℝ) := by
  simp_rw [gramPrefix, Finset.mul_sum]
  rw [show (∑ p ∈ S, ∑ q ∈ S, ∑ n ∈ Finset.Icc 1 N,
        c p*c q*((blockDeletionCoefficient p n:ℝ)*
          (blockDeletionCoefficient q n:ℝ)/(n:ℝ))) =
      ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ S, ∑ q ∈ S,
        c p*c q*((blockDeletionCoefficient p n:ℝ)*
          (blockDeletionCoefficient q n:ℝ)/(n:ℝ)) by
    simp_rw [Finset.sum_comm (s := S) (t := Finset.Icc 1 N)]]
  apply Finset.sum_congr rfl
  intro n _
  rw [pow_two, Finset.sum_mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Positivity belongs to the complete harmonic Gram, before subtracting its residue. -/
theorem gram_quadratic_nonneg (S : Finset ℕ) (c : ℕ → ℝ) (N : ℕ) :
    0 ≤ ∑ p ∈ S, ∑ q ∈ S, c p*c q*gramPrefix p q N := by
  rw [gram_quadratic_eq]
  exact Finset.sum_nonneg (fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

/-- The actual symmetric chronological source; both time orders are retained. -/
def symmetricCross (p q : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  chronologicalCrossPrefix (eulerDeletionWeightedJump p s)
      (eulerDeletionWeightedJump q (partner s)) N +
    star (chronologicalCrossPrefix (eulerDeletionWeightedJump q (partner s))
      (eulerDeletionWeightedJump p s) N)

/-- Full strip limit, including the true endpoint product and every shared-factor boundary. -/
theorem symmetricCross_harmonic_tendsto (p q : ℕ) {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) :
    Tendsto (fun N => symmetricCross p q s N +
      (residue (p+1) (q+1)*(harmonic N:ℝ):ℂ)) atTop
      (nhds (eulerDeletionDirichletSum p s *
        star (eulerDeletionDirichletSum q (partner s))-(finitePart (p+1) (q+1):ℂ))) := by
  have hr : 0 < (partner s).re := by simp [partner]; linarith
  have ht := ((DeletionJointCirculation.source_endpoint_tendsto p hs).mul
    (DeletionJointCirculation.source_endpoint_tendsto q hr).star).sub
      (((tendsto_harmonicPrefix (Nat.succ_pos p)).add
        (tendsto_harmonicPrefix (Nat.succ_pos q))).sub
          ((tendsto_harmonicPrefix
            (Nat.lcm_pos (Nat.succ_pos p) (Nat.succ_pos q))).const_mul
              (Nat.gcd (p+1) (q+1):ℝ))).ofReal
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul] at ht
  have hlim := ht.congr (fun N => (reflected_chronological_decomposition p q N s).symm)
  simpa only [symmetricCross, finitePart, Nat.succ_eq_add_one,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul] using hlim

/-- Reflection's logarithmic normalization includes the Euler constant, with no dropped term. -/
theorem symmetricCross_log_tendsto (p q : ℕ) {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) :
    Tendsto (fun N => symmetricCross p q s N +
      (residue (p+1) (q+1)*Real.log N:ℂ)) atTop
      (nhds (eulerDeletionDirichletSum p s *
        star (eulerDeletionDirichletSum q (partner s))-
          (finitePart (p+1) (q+1)+residue (p+1) (q+1)*
            Real.eulerMascheroniConstant:ℂ))) := by
  have ht := (symmetricCross_harmonic_tendsto p q hs hs').sub
    (Real.tendsto_harmonic_sub_log.const_mul (residue (p+1) (q+1))).ofReal
  convert ht using 1
  · funext N
    push_cast
    ring
  · congr 1
    push_cast
    ring

private theorem endpoint_at_nontrivial_zero (p : ℕ)
    (rho : RiemannGaussian.NontrivialZetaZero) : eulerDeletionDirichletSum p rho.1 = 0 := by
  rw [DeletionJointCirculation.source_endpoint_value p
    (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho) rho.2.2.2, rho.2.1, mul_zero]

/-- Unconditional specialization to every actual zero and its actual reflected zero. -/
theorem symmetricCross_at_nontrivial_zero (p q : ℕ)
    (rho : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (fun N => symmetricCross p q rho.1 N +
      (residue (p+1) (q+1)*(harmonic N:ℝ):ℂ)) atTop
      (nhds (-(finitePart (p+1) (q+1):ℂ))) := by
  simpa only [endpoint_at_nontrivial_zero p rho, zero_mul, zero_sub] using
    symmetricCross_harmonic_tendsto p q
      (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho)
      (RiemannGaussian.NontrivialZetaZero.re_lt_one rho)

/-- The exact logarithmic asymptotic is the same at every actual nontrivial zero. -/
theorem symmetricCross_log_at_nontrivial_zero (p q : ℕ)
    (rho : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (fun N => symmetricCross p q rho.1 N +
      (residue (p+1) (q+1)*Real.log N:ℂ)) atTop
      (nhds (-(finitePart (p+1) (q+1)+residue (p+1) (q+1)*
        Real.eulerMascheroniConstant:ℂ))) := by
  simpa only [endpoint_at_nontrivial_zero p rho, zero_mul, zero_sub] using
    symmetricCross_log_tendsto p q
      (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho)
      (RiemannGaussian.NontrivialZetaZero.re_lt_one rho)

/-- Coprime chronological orders converge separately and are adjoint negatives at actual zeros. -/
theorem coprime_cross_limits_at_nontrivial_zero (p q : ℕ)
    (hpq : (p+1).Coprime (q+1)) (rho : RiemannGaussian.NontrivialZetaZero) :
    ∃ L M : ℂ,
      Tendsto (fun N => chronologicalCrossPrefix (eulerDeletionWeightedJump p rho.1)
        (eulerDeletionWeightedJump q (partner rho.1)) N) atTop (nhds L) ∧
      Tendsto (fun N => chronologicalCrossPrefix (eulerDeletionWeightedJump q (partner rho.1))
        (eulerDeletionWeightedJump p rho.1) N) atTop (nhds M) ∧ L+star M=0 := by
  have hs := RiemannGaussian.NontrivialZetaZero.zero_lt_re rho
  have hr : 0 < (partner rho.1).re := by
    simp only [partner, Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
    linarith [RiemannGaussian.NontrivialZetaZero.re_lt_one rho]
  obtain ⟨L,hL⟩ := tendsto_chronologicalCrossPrefix_eulerDeletion_coprime
    p q rho.1 (partner rho.1) hpq hs hr
  obtain ⟨M,hM⟩ := tendsto_chronologicalCrossPrefix_eulerDeletion_coprime
    q p (partner rho.1) rho.1 hpq.symm hr hs
  refine ⟨L,M,hL,hM,?_⟩
  have hb := coprime_boundary (Nat.succ_pos p) (Nat.succ_pos q) hpq
  have hz : Tendsto (symmetricCross p q rho.1) atTop (nhds 0) := by
    simpa only [hb.1, hb.2, zero_mul, Complex.ofReal_zero, add_zero, neg_zero] using
      symmetricCross_at_nontrivial_zero p q rho
  exact tendsto_nhds_unique (hL.add hM.star) hz

end
end RHTower.DeletionReflectedGram
