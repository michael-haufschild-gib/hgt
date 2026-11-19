import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeMidpointInTwoAdjacentGcdHorizons
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Boundary data for the integer prime midpoint

For integer arguments, division by powers of three ends after finitely
many steps. Arbitrary midpoint observations and arbitrary values at
three-free integers determine a unique price. The homogeneous solutions
can oscillate along a single dyadic orbit even under a linear growth bound.
-/

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Midpoint observation of a price at three integer dilations. -/
def integerMidpointObservation (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  2*f (3*n)-f (2*n)-f (4*n)

/-- Evolution from the three-free row, with an observed forcing at each layer. -/
def ternaryMidpointRow (seed data : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => seed
  | b+1 => fun m => (ternaryMidpointRow seed data b (2*m)+
      ternaryMidpointRow seed data b (4*m)+data (3^b*m))/2

/-- Finite inverse at the exact ternary valuation of the requested integer. -/
def integerMidpointInverse (seed data : ℕ → ℝ) (n : ℕ) : ℝ :=
  ternaryMidpointRow seed data (n.factorization 3) (ordCompl[3] n)

/-- Reading an arbitrary price forward and then inverting recovers each
ternary layer, including at integers that are divisible by other primes. -/
theorem ternary_row_recovers_price (f : ℕ → ℝ) (b m : ℕ) :
    ternaryMidpointRow f (integerMidpointObservation f) b m=f (3^b*m) := by
  induction b generalizing m with
  | zero => simp [ternaryMidpointRow]
  | succ b ih =>
    rw [ternaryMidpointRow,ih,ih,integerMidpointObservation,pow_succ]
    rw [show 3^b*(2*m)=2*(3^b*m) by ac_rfl,
      show 3^b*(4*m)=4*(3^b*m) by ac_rfl,show 3^b*3*m=3*(3^b*m) by ac_rfl]
    ring

private lemma inverse_seed (seed data : ℕ → ℝ) {n : ℕ} (hn : ¬3∣n) :
    integerMidpointInverse seed data n=seed n := by
  simp [integerMidpointInverse,Nat.factorization_eq_zero_of_not_dvd hn,ternaryMidpointRow]

private lemma prime3_times (n : ℕ) (hn : n ≠ 0) :
    (3*n).factorization 3=n.factorization 3+1 ∧ ordCompl[3] (3*n)=ordCompl[3] n := by
  constructor
  · rw [Nat.factorization_mul (by decide) hn,Finsupp.add_apply,Nat.prime_three.factorization_self,Nat.add_comm]
  · simpa only [pow_one] using Nat.ordCompl_self_pow_mul n 1 Nat.prime_three

private lemma three_free_times {j : ℕ} (hj : ¬3∣j) (n : ℕ) (hn : n≠0) :
    (j*n).factorization 3=n.factorization 3 ∧ ordCompl[3] (j*n)=j*ordCompl[3] n := by
  have hj₀ : j ≠ 0 := fun h => hj (h ▸ dvd_zero _)
  constructor
  · rw [Nat.factorization_mul hj₀ hn,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd hj,zero_add]
  · rw [Nat.ordCompl_mul,(Nat.ordCompl_eq_self_iff_zero_or_not_dvd j Nat.prime_three).mpr (Or.inr hj)]

/-- Any prescribed observations are realized on the positive integers. -/
theorem observe_integerMidpointInverse (seed data : ℕ → ℝ) {n : ℕ} (hn : 0<n) :
    integerMidpointObservation (integerMidpointInverse seed data) n=data n := by
  obtain ⟨h₃,e₃⟩ := prime3_times n hn.ne'
  obtain ⟨h₂,e₂⟩ := three_free_times (j:=2) (by decide) n hn.ne'
  obtain ⟨h₄,e₄⟩ := three_free_times (j:=4) (by decide) n hn.ne'
  simp only [integerMidpointObservation,integerMidpointInverse,h₃,e₃,h₂,e₂,h₄,e₄,
    ternaryMidpointRow,Nat.ordProj_mul_ordCompl_eq_self]
  ring

/-- Three-free values are precisely the independent initial data.
There is no compatibility restriction on the prescribed positive-index
observations, and zero has an independent value. -/
theorem unique_integer_midpoint_price (seed data : ℕ → ℝ) :
    ∃! f : ℕ → ℝ, f 0=seed 0 ∧ (∀ n : ℕ, ¬3∣n → f n=seed n) ∧
      ∀ n : ℕ, 0<n → integerMidpointObservation f n=data n := by
  let F := integerMidpointInverse seed data
  have hF₀ : F 0=seed 0 := by simp [F,integerMidpointInverse,ternaryMidpointRow]
  refine ⟨F,⟨hF₀,fun _ => inverse_seed seed data,fun _ => observe_integerMidpointInverse seed data⟩,?_⟩
  rintro f ⟨hf₀,hfs,hfd⟩
  have layer (b m : ℕ) (hm : 0<m) (h₃ : ¬3∣m) : f (3^b*m)=F (3^b*m) := by
    induction b generalizing m with
    | zero => simpa only [pow_zero,one_mul] using (hfs m h₃).trans (inverse_seed seed data h₃).symm
    | succ b ih =>
      have h₁ := hfd (3^b*m) (by positivity)
      have h₂ := observe_integerMidpointInverse seed data (n:=3^b*m) (by positivity)
      change integerMidpointObservation F _=_ at h₂
      have eqj (j : ℕ) (hj : ¬3∣j) (hjpos : 0<j) :
          f (j*(3^b*m))=F (j*(3^b*m)) := by
        rw [show j*(3^b*m)=3^b*(j*m) by ac_rfl]
        exact ih (j*m) (Nat.mul_pos hjpos hm) (fun hd => (Nat.prime_three.dvd_mul.mp hd).elim hj h₃)
      unfold integerMidpointObservation at h₁ h₂
      rw [eqj 2 (by decide) (by decide),eqj 4 (by decide) (by decide)] at h₁
      rw [show 3^(b+1)*m=3*(3^b*m) by rw [pow_succ]; ac_rfl]
      linarith only [h₁,h₂]
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hp
  · exact hf₀.trans hF₀.symm
  · simpa only [Nat.ordProj_mul_ordCompl_eq_self] using layer (n.factorization 3)
      (ordCompl[3] n) (Nat.ordCompl_pos 3 hp.ne') (Nat.not_dvd_ordCompl Nat.prime_three hp.ne')

/-- Exact reconstruction of the ordinary prime price from its midpoint
observations and the three-free boundary values. -/
theorem theta_integer_midpoint_inverse (n : ℕ) :
    Chebyshev.theta n=integerMidpointInverse (fun j : ℕ => Chebyshev.theta j) primeMidpointPrice n := by
  have h : primeMidpointPrice=integerMidpointObservation (fun j : ℕ => Chebyshev.theta j) :=
    funext prime_midpoint_price_eq
  rw [h,integerMidpointInverse,ternary_row_recovers_price,Nat.ordProj_mul_ordCompl_eq_self]

/-- A normalized multiplicative mode. Its two local multipliers are λ at
2 and (λ+2λ²)/3 at 3. -/
def ternaryMidpointMode (λ₀ : ℝ) (n : ℕ) : ℝ :=
  n*λ₀^(n.factorization 2)*((λ₀+2*λ₀^2)/3)^(n.factorization 3)

private lemma mode_mul (l : ℝ) (m n : ℕ) :
    ternaryMidpointMode l (m*n)=ternaryMidpointMode l m*ternaryMidpointMode l n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [ternaryMidpointMode]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ternaryMidpointMode]
  simp only [ternaryMidpointMode,Nat.cast_mul,Nat.factorization_mul hm.ne' hn.ne',Finsupp.add_apply,pow_add]
  ring

/-- Every parameter gives an invisible multiplicative mode. All parameters
in the real unit interval in absolute value give prices of at most linear growth. -/
theorem ternary_modes_are_invisible (l : ℝ) :
    (∀ n, integerMidpointObservation (ternaryMidpointMode l) n=0) ∧
      (|l|≤1 → ∀ n, |ternaryMidpointMode l n|≤n) := by
  have he₂ : ternaryMidpointMode l 2=2*l := by norm_num [ternaryMidpointMode,Nat.prime_two.factorization]
  have he₃ : ternaryMidpointMode l 3=l+2*l^2 := by norm_num [ternaryMidpointMode,Nat.prime_three.factorization]; ring
  constructor
  · intro n
    rw [integerMidpointObservation,mode_mul,mode_mul,mode_mul,show (4:ℕ)=2*2 by decide,
      mode_mul,he₂,he₃]
    ring
  · intro hl n
    have hκ : |(l+2*l^2)/3| ≤ 1 := by
      rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<3)]
      apply (div_le_one (by norm_num)).mpr
      have hsq := pow_le_one₀ (abs_nonneg l) hl 2
      have ht := abs_add_le l (2*l^2)
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),abs_pow] at ht
      linarith only [ht,hsq,hl]
    simp only [ternaryMidpointMode,abs_mul,abs_pow,Nat.abs_cast]
    exact (mul_le_of_le_one_right (by positivity) (pow_le_one₀ (abs_nonneg _) hκ _)).trans
      (mul_le_of_le_one_right (Nat.cast_nonneg _) (pow_le_one₀ (abs_nonneg l) hl _))

#print axioms unique_integer_midpoint_price
#print axioms theta_integer_midpoint_inverse
#print axioms ternary_modes_are_invisible

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
