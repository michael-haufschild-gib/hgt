import GaloisForLFunctions.ExceptionalLayerTheory.LogFactorialWeightsForTheMiddlePrimeInterval
import GaloisForLFunctions.RHTower.VonMangoldtLogSummatory
import GaloisForLFunctions.HTGeometry.CenteredModularAbel

/-!
# Averaging the prime error at a complementary-factor boundary

The centered inner floor primitive is a divisor stencil of zero-mean
modular ramps. Each ramp has a bounded quadratic primitive. After
transposition, each Mangoldt coefficient cuts the averaging interval only once.
-/

noncomputable section
open Finset ArithmeticFunction RHTower HTGeometry
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Difference between the complementary prefix and its period mean,
extended to the zero argument by the same floor formula. -/
def factorialBoundary (R a : ℕ) : ℝ :=
  -factorialPrefix R a-stencil R (fun _ => 1/2)

/-- The zero reciprocal moment removes the drift and the discrete
half-step of the residue mean simultaneously. -/
theorem factorialBoundary_ramps {R : ℕ} (hR : 1 ≤ R) (a : ℕ) :
    factorialBoundary R a=stencil R (fun d => centeredModularRamp d a) := by
  let g (d : ℕ) := ((a : ℝ)+1/2)/d-((a/d : ℕ) : ℝ)-1/2
  have hc (d : ℕ) (hd : d ∈ Icc 1 (2*R)) : centeredModularRamp d a=g d := by
    have hd₀ : (d : ℝ) ≠ 0 := by exact_mod_cast ((mem_Icc.mp hd).1 : 0<d).ne'
    have hid : (d : ℝ)*((a/d : ℕ) : ℝ)+((a%d : ℕ) : ℝ)=a := by exact_mod_cast Nat.div_add_mod a d
    dsimp [g,centeredModularRamp]
    field_simp
    linarith only [hid]
  have hz := abs_stencil_le hR (fun d => centeredModularRamp d a-g d) (M := 0)
    (fun d hd => by rw [hc d hd,sub_self,abs_zero])
  rw [mul_zero,stencil_sub,abs_le] at hz
  have eq : stencil R (fun d => centeredModularRamp d a)=stencil R g := by linarith only [hz.1,hz.2]
  dsimp only [g] at eq
  rw [stencil_sub,stencil_sub,stencil_linear_quotient hR,zero_sub] at eq
  exact eq.symm

/-- Every integer interval has boundary-coefficient discrepancy bounded
by a quarter of the stencil mass times its scale. -/
theorem factorialBoundary_interval {R : ℕ} (hR : 1 ≤ R) (L U : ℕ) :
    |∑ a ∈ Ico L U, factorialBoundary R a| ≤ mass R*((R : ℝ)/4) := by
  by_cases hlu : L ≤ U
  swap
  · rw [Ico_eq_empty (by omega),sum_empty,abs_zero]
    have hm := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
    positivity
  simp_rw [factorialBoundary_ramps hR]
  have h := stencil_weighted_sum R (Ico L U) (fun _ => 1) (fun a d => centeredModularRamp d a)
  simp only [one_mul] at h
  rw [h]
  apply abs_stencil_le hR
  intro d hd
  rw [sum_Ico_eq_sub _ hlu,sum_centeredModularRamp,sum_centeredModularRamp,abs_le]
  have h₁ := centeredModularPrimitive_bounds d L
  have h₂ := centeredModularPrimitive_bounds d U
  have ht : (d : ℝ) ≤ 2*R := by exact_mod_cast (mem_Icc.mp hd).2
  constructor <;> linarith only [h₁.1,h₁.2,h₂.1,h₂.2,ht]

/-- The moving Chebyshev error at a smoothed complementary-factor cutoff
costs only the reciprocal horizon times the second stencil mass. -/
theorem factorialBoundary_prime_error {R : ℕ} (hR : 1 ≤ R) (X A B : ℕ) :
    |∑ a ∈ Ico A B, factorialBoundary R a*
      (Chebyshev.psi (X/(a+1) : ℕ)-(X/(a+1) : ℕ))| ≤
      2*mass R*R*(X/(A+1) : ℕ) := by
  let U := X/(A+1)
  let e (n : ℕ) := vonMangoldt n-1
  let b := factorialBoundary R
  have err (a : ℕ) (ha : A ≤ a) : Chebyshev.psi (X/(a+1) : ℕ)-(X/(a+1) : ℕ) =
      ∑ n ∈ Icc 1 U, if a<X/n then e n else 0 := by
    let T := X/(a+1)
    have htu : T ≤ U := (Nat.le_div_iff_mul_le (Nat.succ_pos A)).mpr
      ((Nat.mul_le_mul_left T (Nat.succ_le_succ ha)).trans (Nat.div_mul_le_self X (a+1)))
    have eq : (Icc 1 U).filter (fun n => a<X/n)=Icc 1 T := by
      ext n
      constructor
      · intro hn
        obtain ⟨hi,hl⟩ := mem_filter.mp hn
        have hn₁ := (mem_Icc.mp hi).1
        have hh := (Nat.le_div_iff_mul_le hn₁).mp (show a+1 ≤ X/n from hl)
        exact mem_Icc.mpr ⟨hn₁,(Nat.le_div_iff_mul_le (Nat.succ_pos a)).mpr (by simpa only [Nat.mul_comm n] using hh)⟩
      · intro hn
        obtain ⟨hl,hu⟩ := mem_Icc.mp hn
        have hh := (Nat.le_div_iff_mul_le (Nat.succ_pos a)).mp hu
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hl,hu.trans htu⟩,(Nat.le_div_iff_mul_le hl).mpr
          (by simpa only [Nat.mul_comm n] using hh)⟩
    rw [←sum_filter,eq]
    have hp : (∑ n ∈ Icc 1 T, vonMangoldt n)=Chebyshev.psi T := by
      unfold Chebyshev.psi; rw [Nat.floor_natCast]; rfl
    simp only [e,sum_sub_distrib,hp,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_one]
    rfl
  have transpose : (∑ a ∈ Ico A B, b a*(Chebyshev.psi (X/(a+1) : ℕ)-(X/(a+1) : ℕ))) =
      ∑ n ∈ Icc 1 U, e n*∑ a ∈ Ico A (min B (X/n)), b a := by
    calc _ = ∑ a ∈ Ico A B, ∑ n ∈ Icc 1 U, if a<X/n then e n*b a else 0 := by
              apply sum_congr rfl
              intro a ha
              rw [err a (mem_Ico.mp ha).1,mul_sum]
              exact sum_congr rfl fun n _ => by by_cases h : a<X/n <;> simp [h,mul_comm]
         _ = _ := by
              rw [sum_comm]
              apply sum_congr rfl
              intro n _
              have eq : (Ico A B).filter (fun a => a<X/n)=Ico A (min B (X/n)) := by
                ext a; simp only [mem_filter,mem_Ico,lt_min_iff]; tauto
              rw [←sum_filter,eq,mul_sum]
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
  let H := mass R*((R : ℝ)/4)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  rw [transpose]
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ n ∈ Icc 1 U, H*(vonMangoldt n+1) := by
            apply sum_le_sum
            intro n _
            have hn : |e n| ≤ vonMangoldt n+1 := by
              simpa only [abs_of_nonneg vonMangoldt_nonneg,abs_one] using abs_sub (vonMangoldt n) (1 : ℝ)
            rw [abs_mul,mul_comm H]
            exact mul_le_mul hn (factorialBoundary_interval hR _ _) (abs_nonneg _) (by positivity)
       _ ≤ _ := by
            rw [←mul_sum,sum_add_distrib,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_one]
            calc H*((∑ n ∈ Icc 1 U, vonMangoldt n)+(U : ℝ)) ≤ H*(7*U+U) :=
                    mul_le_mul_of_nonneg_left (add_le_add (chebyshevPsi_le_seven U) (le_refl (U : ℝ))) hH
                 _ = _ := by dsimp [H,U]; ring

/-- Averaging over just more than the square root divided by the initial
cutoff gives square-root error at every horizon and cutoff. -/
theorem factorialBoundary_smoothed_prime_error {R : ℕ} (hR : 1 ≤ R) (X A : ℕ) :
    let S := ⌊Real.sqrt X/(A+1 : ℕ)⌋₊+1
    |(∑ a ∈ Ico A (A+S), factorialBoundary R a*
      (Chebyshev.psi (X/(a+1) : ℕ)-(X/(a+1) : ℕ)))/(S : ℝ)| ≤
      2*mass R*R*Real.sqrt X := by
  intro S
  have hS : (0 : ℝ) < S := by exact_mod_cast (Nat.succ_pos _ : 0<S)
  have ha : (0 : ℝ) < (A+1 : ℕ) := by positivity
  have hl : Real.sqrt X/(A+1 : ℕ) ≤ (S : ℝ) := by
    dsimp only [S]; push_cast
    exact (Nat.lt_floor_add_one _).le
  have hs := (div_le_iff₀ ha).mp hl
  have hu : ((X/(A+1) : ℕ) : ℝ) ≤ Real.sqrt X*S := by
    apply Nat.cast_div_le.trans
    apply (div_le_iff₀ ha).mpr
    exact (Real.mul_self_sqrt (Nat.cast_nonneg X)).symm.le.trans
      ((mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)).trans_eq (by ring))
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
  rw [abs_div,abs_of_nonneg hS.le]
  apply (div_le_iff₀ hS).mpr
  exact (factorialBoundary_prime_error hR X A (A+S)).trans
    ((mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 2*mass R*R)).trans_eq (by ring))

#print axioms factorialBoundary_smoothed_prime_error
#print axioms factorialBoundary_interval
#print axioms factorialBoundary_prime_error
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
