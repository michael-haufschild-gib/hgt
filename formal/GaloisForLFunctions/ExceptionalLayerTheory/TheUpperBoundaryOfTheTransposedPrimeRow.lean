import GaloisForLFunctions.ExceptionalLayerTheory.TransposingTheComplementaryFactorTail
import GaloisForLFunctions.ExceptionalLayerTheory.TheDualDivisorStencilInTheSquareRootProductWindow

/-!
# The upper boundary of the transposed prime row

Below the square root the number of second factors retains a reciprocal
prime weight. Above it the dual divisor stencil acts on the complete
prime product window, with the original second-factor coefficients.
-/

noncomputable section
open Finset RHTower ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Upper boundary in a transposed quotient sum, with freely varying
product threshold and signed second coefficients. -/
def dualBoundaryHead (X R F U : ℕ) (β : ℕ → ℝ) : ℝ :=
  ordinaryFactorTail F X (fun p => ∑ j ∈ Icc 1 (U/p), β j*factorialBoundary R (X/(p*j)))

private theorem head_by_second {X U : ℕ} (hu : U≤X) (R F : ℕ) (β : ℕ → ℝ) :
    dualBoundaryHead X R F U β = ∑ j ∈ Icc 1 X, β j*
      ∑ p ∈ squareRootWindowPrimes F 0 U j, Real.log p*factorialBoundary R (X/(p*j)) := by
  let P := (Ioc F X).filter Nat.Prime
  let f (p j : ℕ) := Real.log p*(β j*factorialBoundary R (X/(p*j)))
  calc _ = ∑ p ∈ P, ∑ j ∈ Icc 1 X, if p*j≤U then f p j else 0 := by
            unfold dualBoundaryHead ordinaryFactorTail
            apply sum_congr rfl; intro p hp
            obtain ⟨_,hp'⟩ := mem_filter.mp hp
            have eq : (Icc 1 X).filter (fun j => p*j≤U)=Icc 1 (U/p) := by
              ext j
              simp only [mem_filter,mem_Icc,Nat.le_div_iff_mul_le hp'.pos,Nat.mul_comm j p]
              have aux : p*j≤U → j≤X := fun h => ((Nat.le_div_iff_mul_le hp'.pos).mpr
                (by rwa [Nat.mul_comm] at h)).trans ((Nat.div_le_self U p).trans hu)
              tauto
            rw [←sum_filter,eq,vonMangoldt_apply_prime hp',mul_sum]
       _ = _ := by
            rw [sum_comm]; apply sum_congr rfl; intro j hj
            have hj₁ := (mem_Icc.mp hj).1
            have eq : P.filter (fun p => p*j≤U)=squareRootWindowPrimes F 0 U j := by
              rw [squareRootWindowPrimes_eq_filter hj₁ hu]
              ext p
              simp only [P,mem_filter,mem_Ico,mem_Ioc,Nat.lt_succ_iff,Nat.succ_le_iff]
              constructor
              · rintro ⟨⟨h,hp⟩,hU⟩; exact ⟨h,hp,Nat.mul_pos hp.pos hj₁,hU⟩
              · rintro ⟨h,hp,_,hU⟩; exact ⟨⟨h,hp⟩,hU⟩
            rw [←sum_filter,eq,mul_sum]
            exact sum_congr rfl fun p _ => by dsimp only [f]; ring

/-- Subtracting two heads retains exactly the primes in the open-closed
product interval. -/
theorem dualBoundaryHead_sub {L U X : ℕ} (hl : L≤U) (hu : U≤X) (R F : ℕ) (β : ℕ → ℝ) :
    dualBoundaryHead X R F U β-dualBoundaryHead X R F L β =
      ∑ j ∈ Icc 1 X, β j*∑ p ∈ squareRootWindowPrimes F L U j,
        Real.log p*factorialBoundary R (X/(p*j)) := by
  rw [head_by_second hu,head_by_second (hl.trans hu),←sum_sub_distrib]
  apply sum_congr rfl; intro j hj
  rw [←mul_sub]
  congr 1
  let S := squareRootWindowPrimes F 0 U j
  let f (p : ℕ) := Real.log p*factorialBoundary R (X/(p*j))
  have hj₁ := (mem_Icc.mp hj).1
  have lo : S.filter (fun p => p*j≤L)=squareRootWindowPrimes F 0 L j := by
    dsimp only [S]
    rw [squareRootWindowPrimes_eq_filter hj₁ hu,squareRootWindowPrimes_eq_filter hj₁ (hl.trans hu)]
    ext p; simp only [mem_filter]; exact ⟨fun h => ⟨h.1.1,h.1.2.1,h.1.2.2.1,h.2⟩,
      fun h => ⟨⟨h.1,h.2.1,h.2.2.1,h.2.2.2.trans hl⟩,h.2.2.2⟩⟩
  have hi : S.filter (fun p => ¬p*j≤L)=squareRootWindowPrimes F L U j := by
    dsimp only [S]
    rw [squareRootWindowPrimes_eq_filter hj₁ hu,squareRootWindowPrimes_eq_filter hj₁ hu]
    ext p; simp only [mem_filter,not_le]
    exact ⟨fun h => ⟨h.1.1,h.1.2.1,h.2,h.1.2.2.2⟩,fun h =>
      ⟨⟨h.1,h.2.1,(Nat.zero_le L).trans_lt h.2.2.1,h.2.2.2⟩,h.2.2.1⟩⟩
  have eq := sum_filter_add_sum_filter_not S (fun p => p*j≤L) f
  rw [lo,hi] at eq
  exact sub_eq_of_eq_add (eq.symm.trans (add_comm ..))

private theorem abs_boundary {R : ℕ} (hR : 1≤R) (n : ℕ) : |factorialBoundary R n|≤2*mass R := by
  have h := abs_stencil_le hR (fun _ => (1/2 : ℝ)) (M := 1) (fun _ _ => by norm_num)
  rw [mul_one] at h
  unfold factorialBoundary
  apply (abs_sub _ _).trans
  rw [abs_neg]
  linarith only [abs_prefix_le_mass hR n,h]

private theorem head_cost {X R F U : ℕ} (hx : 1≤X) (hR : 1≤R) (β : ℕ → ℝ)
    {M : ℝ} (hM : 0≤M) (hβ : ∀ j, |β j|≤M) :
    |dualBoundaryHead X R F U β|≤(M*(2*mass R)*U)*((Real.log 4+4)*(1+Real.log X)) := by
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
  apply ordinaryFactorTail_reciprocal hx (by positivity)
  intro p _
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _j ∈ Icc 1 (U/p), M*(2*mass R) := by
            apply sum_le_sum; intro j _
            rw [abs_mul]
            exact mul_le_mul (hβ j) (abs_boundary hR _) (abs_nonneg _) hM
       _ ≤ _ := by
            rw [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
            exact (mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity : 0≤M*(2*mass R))).trans_eq (by ring)

/-- Square-root control of the complete transposed upper boundary,
including all products below the dual window and arbitrary signed jumps. -/
theorem dualBoundaryHead_bound :
    ∃ K : ℝ, 0≤K ∧ ∀ {X R F U : ℕ}, 1≤X → 1≤R →
    64≤(X : ℝ)^(1/25000000 : ℝ) → ((2*R : ℕ) : ℝ)≤(X : ℝ)^(1/25000000 : ℝ) →
    ⌊(X : ℝ)^(1/1000000 : ℝ)⌋₊≤F → (U : ℝ)≤(X : ℝ)^(500000001/1000000000 : ℝ) →
    ∀ (β : ℕ → ℝ) {M : ℝ}, 0≤M → (∀ j, |β j|≤M) →
      |dualBoundaryHead X R F U β|≤K*mass R*M*(1+Real.log X)^3*Real.sqrt X := by
  obtain ⟨K,hK,h⟩ := dual_factorial_window
  let E := Real.log 4+4
  have hE : 0≤E := add_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ)≤4)) (by norm_num)
  refine ⟨2*E+K,by positivity,?_⟩
  intro X R F U hx hR hbig hd hF hU β M hM hβ
  let L := min U ⌊Real.sqrt X⌋₊
  let J := 1+Real.log X
  have hJ : 1≤J := le_add_of_nonneg_right (Real.log_natCast_nonneg _)
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
  have hx₁ : (1 : ℝ)≤X := by exact_mod_cast hx
  have hu : U≤X := by exact_mod_cast hU.trans ((Real.rpow_le_rpow_of_exponent_le hx₁
    (by norm_num : (500000001/1000000000 : ℝ)≤1)).trans_eq (Real.rpow_one _))
  have hlo : (L : ℝ)≤Real.sqrt X := (by exact_mod_cast min_le_right U ⌊Real.sqrt X⌋₊ :
    (L : ℝ)≤⌊Real.sqrt X⌋₊).trans (Nat.floor_le (Real.sqrt_nonneg _))
  have small : |dualBoundaryHead X R F L β|≤2*E*mass R*M*J^3*Real.sqrt X := by
    apply (head_cost (F := F) (U := L) hx hR β hM hβ).trans
    have h1 := mul_le_mul_of_nonneg_left hlo (show 0≤M*(2*mass R) by positivity)
    have h2 : J≤J^3 := by simpa only [pow_one] using pow_le_pow_right₀ hJ (by norm_num : 1≤3)
    have h3 := mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hE)
      (mul_nonneg hE (zero_le_one.trans hJ)) (by positivity)
    change M*(2*mass R)*L*(E*J)≤_
    linarith only [h3]
  have large : |dualBoundaryHead X R F U β-dualBoundaryHead X R F L β|≤
      mass R*(K*M*J^3*Real.sqrt X) := by
    by_cases hle : U≤⌊Real.sqrt X⌋₊
    · simp only [L,min_eq_left hle,sub_self,abs_zero]
      exact mul_nonneg hm (by have := zero_le_one.trans hJ; positivity)
    · rw [dualBoundaryHead_sub (min_le_left ..) hu]
      have hl : Real.sqrt X≤(L : ℝ)+1 := by
        rw [show L=⌊Real.sqrt X⌋₊ from min_eq_right (le_of_not_ge hle)]
        exact (Nat.lt_floor_add_one _).le
      exact h hx hR hbig hd hF hl hU β hM (fun j _ => hβ j)
  have hh := abs_add_le (dualBoundaryHead X R F U β-dualBoundaryHead X R F L β) (dualBoundaryHead X R F L β)
  rw [sub_add_cancel] at hh
  exact hh.trans ((add_le_add large small).trans_eq (by ring))

#print axioms dualBoundaryHead_bound
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
