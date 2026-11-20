import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.RecoveringPrimePairsFromTranslatedMidpoints

/-!
# Variation loss and prime pairs in a sharp midpoint

The negative variation records all lower-half prime weights except those
having a prime partner in the upper half. The lost variation and the lost
squared slope energy give two different exact correlations at gap n.
-/
noncomputable section
open Finset Complex
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.MidpointFourier

private def leftSite (n j : ℕ) := 2*n+1+j
/-- Selected logarithmic weight at the lower member of an opposite pair. -/
def lower (P : ℕ → Bool) (n j : ℕ) := selectedLog P (leftSite n j)
/-- Selected logarithmic weight at the upper member of an opposite pair. -/
def upper (P : ℕ → Bool) (n j : ℕ) := selectedLog P (leftSite n j+n)

private def changeInPrice (P : ℕ → Bool) (n j : ℕ) :=
  midpointReading n P (j+1)-midpointReading n P j

/-- Ordered pair count with lower-endpoint logarithmic weight. -/
def pairedLog (P : ℕ → Bool) (n : ℕ) : ℝ :=
  ∑ j∈range n,if P (leftSite n j+n) then lower P n j else 0

private theorem change_eq (P : ℕ → Bool) {n j : ℕ} (hj : j<n) :
    changeInPrice P n j=2*(upper P n j-lower P n j) := logarithmic_midpoint_step hj P

private theorem local_variation (P : ℕ → Bool) {n j : ℕ} (hj : j<n) :
    abs (changeInPrice P n j)=
      2*(upper P n j+lower P n j)-4*(if P (leftSite n j+n) then lower P n j else 0) := by
  rw [change_eq P hj]
  have hl : 0≤Real.log (leftSite n j:ℕ) := Real.log_natCast_nonneg _
  have hr : 0≤Real.log (leftSite n j+n:ℕ) := Real.log_natCast_nonneg _
  have hm : Real.log (leftSite n j:ℕ)≤Real.log (leftSite n j+n:ℕ) :=
    Real.log_le_log (Nat.cast_pos.mpr (by dsimp [leftSite];omega)) (by exact_mod_cast (Nat.le_add_right (leftSite n j) n))
  cases ha : P (leftSite n j) <;> cases hb : P (leftSite n j+n) <;>
    simp only [lower,upper,selectedLog,ha,hb,Bool.false_eq_true,if_false,if_true,
      abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),sub_zero,zero_sub,abs_neg,abs_zero,
      abs_of_nonneg hl,abs_of_nonneg hr,abs_of_nonneg (sub_nonneg.mpr hm)] <;> ring

/-- Total variation over n independent price changes, with the exact
debit contributed by every pair of primes whose separation is n. -/
theorem sharp_midpoint_variation (P : ℕ → Bool) (n : ℕ) :
    (∑ j∈range n,abs (midpointReading n P (j+1)-midpointReading n P j))=
      2*(∑ j∈range n,(upper P n j+lower P n j))-4*pairedLog P n := by
  rw [pairedLog,mul_sum,mul_sum,←sum_sub_distrib]
  exact sum_congr rfl fun j hj => local_variation P (mem_range.mp hj)

/-- Quadratic variation determines the product-weighted pair sum, while
the ordinary variation determines the lower-logarithm pair sum. -/
theorem sharp_midpoint_quadratic_variation (P : ℕ → Bool) (n : ℕ) :
    (∑ j∈range n,(midpointReading n P (j+1)-midpointReading n P j)^2)=
      4*(∑ j∈range n,((upper P n j)^2+(lower P n j)^2))-
      8*(∑ j∈range n,lower P n j*upper P n j) := by
  rw [mul_sum,mul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  change (changeInPrice P n j)^2=_
  rw [change_eq P (mem_range.mp hj)]
  ring

/-- The variation of the actual prime price saturates its diagonal bound
if and only if the interval contains no ordinary-prime pair at displacement n. -/
theorem prime_midpoint_full_variation_iff (n : ℕ) :
    (∑ j∈range n,abs (midpointReading n (fun x => decide x.Prime) (j+1)-
      midpointReading n (fun x => decide x.Prime) j))=
       2*∑ j∈range n,(upper (fun x => decide x.Prime) n j+lower (fun x => decide x.Prime) n j) ↔
      ∀ m∈Ioc (2*n) (3*n),m.Prime → ¬(m+n).Prime := by
  let P := fun m : ℕ => decide m.Prime
  rw [sharp_midpoint_variation,sub_eq_self,mul_eq_zero]
  simp only [OfNat.ofNat_ne_zero,false_or]
  have hpos (j : ℕ) : 0≤(if P (leftSite n j+n) then lower P n j else 0) := by
    dsimp only [lower,selectedLog]; split_ifs <;> first | exact Real.log_natCast_nonneg _ | exact le_rfl
  change (∑ j∈range n,if P (leftSite n j+n) then lower P n j else 0)=0 ↔ _
  rw [sum_eq_zero_iff_of_nonneg (fun j _ => hpos j)]
  constructor
  · intro hh m hm hp hq
    let j := m-(2*n+1)
    have hlo := (mem_Ioc.mp hm).1
    have hhi := (mem_Ioc.mp hm).2
    have hj : j<n := by dsimp [j];omega
    have he : leftSite n j=m := by dsimp [leftSite,j];omega
    have hz := hh j (mem_range.mpr hj)
    simp [P,he,hq,lower,selectedLog,hp] at hz
    exact (Real.log_pos (show (1:ℝ)< m by exact_mod_cast hp.one_lt)).ne' hz
  · intro h j hj
    have hm : leftSite n j∈Ioc (2*n) (3*n) := by
      have h' := mem_range.mp hj
      exact mem_Ioc.mpr ⟨by dsimp [leftSite];omega, by dsimp [leftSite];omega⟩
    by_cases hp : (leftSite n j).Prime
    · simp [P,h _ hm hp]
    · simp [P,lower,selectedLog,hp]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.MidpointFourier
