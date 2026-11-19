import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SignedDivisibilityAveragesOfTheReflectedCofactors
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheClippedCofactorDensityAtThePrimeMidpoint

/-!
# Ordinary prime intervals under signed sampling of the midpoint

Freeze the three prime endpoints before averaging the primitive restrictions.
The coefficient of each centered cofactor interval then has an explicit
divisor sum. Quotient windows may start at different integers.
-/

noncomputable section
open Finset GaloisForLFunctions.ArithmeticEffectivityTheory
open RHTower (truncMoebiusDivisorSum)
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Right-minus-left ordinary prime price, less its clipped continuous length. -/
def centeredOrdinaryCofactorInterval (n Q v : ℕ) : ℝ :=
  Chebyshev.theta (max Q (4*n/v):ℕ) - 2*Chebyshev.theta (max Q (3*n/v):ℕ) +
    Chebyshev.theta (max Q (2*n/v):ℕ) - reflectedCofactorLength n Q v

/-- The endpoints are those of n and the primitive restriction is that of m. -/
def frozenOrdinaryCofactorPrice (n Q m : ℕ) : ℝ :=
  ∑ v ∈ (Icc 2 (4*n/Q)).filter (·.Coprime m), centeredOrdinaryCofactorInterval n Q v

/-- The projected price starts strictly beyond the divisibility cutoff. -/
def projectedOrdinaryCofactorPrice (n Q V : ℕ) : ℝ :=
  ∑ v ∈ Ioc V (4*n/Q), (v.totient:ℝ)/v*truncMoebiusDivisorSum V v*
    centeredOrdinaryCofactorInterval n Q v

private theorem frozen_window (n Q d a L : ℕ) :
    (∑ k ∈ Ioc a (a+L), frozenOrdinaryCofactorPrice n Q (d*k))/L =
      ∑ v ∈ Icc 2 (4*n/Q), sampledCofactorFrequency v d a L*
        centeredOrdinaryCofactorInterval n Q v := by
  simp only [frozenOrdinaryCofactorPrice,sum_filter,sampledCofactorFrequency]
  rw [sum_comm,sum_div]
  apply sum_congr rfl
  intro v _
  rw [div_mul_eq_mul_div, sum_mul]
  exact congrArg (fun z : ℝ => z/L) (sum_congr rfl fun k _ => by split_ifs <;> simp)

private theorem projected_price_over_all (n Q : ℕ) {V : ℕ} (hV : 1 ≤ V) :
    projectedOrdinaryCofactorPrice n Q V =
      ∑ v ∈ Icc 2 (4*n/Q), (v.totient:ℝ)/v*truncMoebiusDivisorSum V v*
        centeredOrdinaryCofactorInterval n Q v := by
  apply sum_subset
  · intro v hv
    obtain ⟨hl,hr⟩ := mem_Ioc.mp hv
    exact mem_Icc.mpr ⟨by omega,hr⟩
  · intro v hv hx
    obtain ⟨hl,hr⟩ := mem_Icc.mp hv
    have hvV : v ≤ V := by simpa only [mem_Ioc,hr,and_true,not_lt] using hx
    rw [_root_.RHTower.truncMoebiusDivisorSum_of_le (by omega) hvV,if_neg (by omega),mul_zero,zero_mul]

/-- Signed averages of genuine ordinary prime intervals. Only the squarefree
divisor mass of each cofactor enters the finite-window discrepancy. -/
theorem signed_ordinary_cofactor_window (n Q : ℕ) {V : ℕ} (hV : 1 ≤ V) (a L : ℕ → ℕ)
    (hL : ∀ d ∈ Icc 1 V, 0 < L d) :
    |(∑ d ∈ Icc 1 V, mertens (V/d)*
      ((∑ k ∈ Ioc (a d) (a d+L d), frozenOrdinaryCofactorPrice n Q (d*k))/(L d:ℝ)))-
      projectedOrdinaryCofactorPrice n Q V| ≤
      (∑ v ∈ Icc 2 (4*n/Q), squarefreeDivisorMass v*|centeredOrdinaryCofactorInterval n Q v|)*
      ∑ d ∈ Icc 1 V, |mertens (V/d)| / (L d:ℝ) := by
  let Δ := centeredOrdinaryCofactorInterval n Q
  rw [projected_price_over_all n Q hV]
  simp only [frozen_window,mul_sum,←mul_assoc]
  rw [sum_comm]
  simp only [←sum_mul,←sum_sub_distrib,←sub_mul]
  apply (abs_sum_le_sum_abs _ _).trans
  rw [sum_mul]
  apply sum_le_sum
  intro v hv
  have h := signed_window_cofactor_density V (v:=v) (by have := (mem_Icc.mp hv).1; omega) a L hL
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right h (abs_nonneg (Δ v))).trans_eq (by ring)

#print axioms signed_ordinary_cofactor_window

/-- A window of H consecutive integers has at least ⌊H/d⌋ multiples of d.
The endpoint loss after signed sampling is at most twice the first moment
of the divisibility weights divided by H. -/
theorem ordinary_cofactor_window_cost {V H : ℕ} (hV : 1 ≤ V) (hVH : V ≤ H)
    (L : ℕ → ℕ) (hL : ∀ d ∈ Icc 1 V, H/d ≤ L d) :
    (∑ d ∈ Icc 1 V, |mertens (V/d)| / (L d:ℝ)) ≤ 2*(V:ℝ)^2/H := by
  have hH := (Nat.cast_pos (α:=ℝ)).mpr (lt_of_lt_of_le (by omega : 0 < V) hVH)
  rw [le_div_iff₀ hH,sum_mul]
  have hcost := (cofactor_projection_weight_cost V).2
  calc _ ≤ ∑ d ∈ Icc 1 V, 2*((d:ℝ)*|mertens (V/d)|) := by
             apply sum_le_sum
             intro d hd
             obtain ⟨hd0,hdV⟩ := mem_Icc.mp hd
             have hdH := hdV.trans hVH
             have hq := Nat.div_pos hdH hd0
             have hlen := hL d hd
             have hlt := Nat.lt_mul_div_succ H hd0
             have h1 := Nat.mul_le_mul_left d hq
             have h2 := Nat.mul_le_mul_left d hlen
             have hlen' := (Nat.cast_pos (α:=ℝ)).mpr (hq.trans_le hlen)
             have hbound : (H:ℝ) ≤ 2*((d:ℝ)*(L d:ℝ)) := by
               have hnat : H ≤ 2*(d*L d) := by
                 rw [Nat.mul_succ] at hlt
                 rw [Nat.mul_one] at h1
                 omega
               exact_mod_cast hnat
             calc _ = |mertens (V/d)| * ((H:ℝ)/L d) := by ring
                  _ ≤ |mertens (V/d)| * (2*d) := mul_le_mul_of_nonneg_left
                    ((div_le_iff₀ hlen').mpr (by linarith only [hbound])) (abs_nonneg _)
                  _ = _ := by ring
       _ ≤ _ := by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left hcost (by norm_num)

#print axioms ordinary_cofactor_window_cost

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
