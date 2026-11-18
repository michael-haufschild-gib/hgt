import GaloisForLFunctions.ExceptionalLayerTheory.CancellationAcrossComplementaryFactorSlices
import GaloisForLFunctions.ExceptionalLayerTheory.ReciprocalPrimeCancellationInTheCoprimeProduct

/-!
# Removing small ordinary first primes at both Vaughan widths

At each fixed prime the entire complementary-factor slice saves a power
at its divided horizon. Summing over small primes still costs at most
square-root error up to logarithms. These primes are disjoint from the
previous reciprocal band above the lower product cutoff.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- First primes below a fixed power of the horizon. -/
def shortFirstPrimes (D X : ℕ) : Finset ℕ :=
  (Ioc (2*(D+1)) (min X ⌊(X : ℝ)^(1/200 : ℝ)⌋₊)).filter Nat.Prime

/-- The whole complementary-factor row on short ordinary first primes,
with coprimality imposed at every product. -/
def shortFirstRow (D R X Y : ℕ) : ℝ :=
  ∑ p ∈ shortFirstPrimes D X, vonMangoldt p*coprimeSlice D R X Y p

/-- Uniform cost of the small first primes, including the shared-prime
correction, even when the lower product endpoint cuts a quotient fibre. -/
theorem short_first_row_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {D R X : ℕ}, 1 ≤ D → 1 ≤ R → 1 ≤ X → ∀ Y : ℕ,
      |shortFirstRow D R X Y| ≤ K*(((D+1 : ℕ) : ℝ)^2*(R : ℝ)^3*(X : ℝ)^(99/200 : ℝ)+
        ((D+1 : ℕ) : ℝ)*R*Real.sqrt X)*(1+Real.log X) := by
  obtain ⟨C,hC,h⟩ := complementary_slice_power_bound
  obtain ⟨B,hB,hs⟩ := factor_slice_bounds
  let M := Real.log 4+4
  have hM : 1 ≤ M := by dsimp [M]; linarith only [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  refine ⟨7*C+B*M,by positivity,?_⟩
  intro D R X hD hR hx Y
  let S := shortFirstPrimes D X
  let Q := ⌊(X : ℝ)^(1/200 : ℝ)⌋₊
  let A := C*((D+1 : ℕ) : ℝ)^2*(R : ℝ)^3*(1+Real.log X)*(X : ℝ)^(49/100 : ℝ)
  let E := B*((D+1 : ℕ) : ℝ)*R*Real.sqrt X
  have hlog := Real.log_natCast_nonneg X
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have mem {p : ℕ} (hp : p ∈ S) : 2*(D+1)<p ∧ p ≤ X ∧ p ≤ Q ∧ p.Prime := by
    obtain ⟨hi,prime⟩ := mem_filter.mp hp
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hi
    exact ⟨hl,hu.trans (min_le_left ..),hu.trans (min_le_right ..),prime⟩
  have he (p : ℕ) (hp : p ∈ S) : |coprimeSlice D R X Y p| ≤ A+E/p := by
    obtain ⟨hl,hu,_,prime⟩ := mem hp
    have ht := (Nat.one_le_div_iff prime.pos).mpr hu
    have hh := h (D := D) hR ht (Y/p)
    have hTx : ((X/p : ℕ) : ℝ) ≤ X := by exact_mod_cast Nat.div_le_self X p
    have h₁ := Real.log_le_log (by exact_mod_cast ht : (0 : ℝ) < (X/p : ℕ)) hTx
    have h₂ := Real.rpow_le_rpow (Nat.cast_nonneg (X/p)) hTx (by norm_num : (0 : ℝ) ≤ 49/100)
    have hb : |factorSlice D R X Y p| ≤ A := hh.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (add_le_add_left h₁ 1) (by positivity)) h₂ (by positivity) (by positivity))
    have hc := (hs hD hR X Y).2 p prime hl
    have id : coprimeSlice D R X Y p =
        factorSlice D R X Y p-(factorSlice D R X Y p-coprimeSlice D R X Y p) := by ring
    rw [id]
    exact (abs_sub _ _).trans (add_le_add hb hc)
  have hmass : ∑ p ∈ S, vonMangoldt p ≤ 7*(X : ℝ)^(1/200 : ℝ) := by
    apply (le_trans _ (chebyshevPsi_le_seven Q)).trans
      (mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by norm_num))
    apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => vonMangoldt_nonneg)
    intro p hp
    obtain ⟨_,_,hu,prime⟩ := mem hp
    exact mem_Icc.mpr ⟨prime.pos,hu⟩
  have hmert : (∑ p ∈ S, vonMangoldt p/p) ≤ M*(1+Real.log X) := by
    have hsub : S ⊆ Icc 1 X := fun p hp => mem_Icc.mpr ⟨(mem hp).2.2.2.pos,(mem hp).2.1⟩
    apply (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))).trans
    have hh := (abs_le.mp (Mertens.mertens_first X hx)).2
    change _ ≤ M*(1+Real.log X)
    have hm := mul_le_mul_of_nonneg_right hM hlog
    dsimp [M] at hm ⊢
    linarith only [hh,hm]
  have hexp : (X : ℝ)^(49/100 : ℝ)*(X : ℝ)^(1/200 : ℝ)=(X : ℝ)^(99/200 : ℝ) := by
    rw [←Real.rpow_add (by exact_mod_cast hx : (0 : ℝ) < X)]; norm_num
  unfold shortFirstRow
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ p ∈ S, (A*vonMangoldt p+E*(vonMangoldt p/p)) := by
            apply sum_le_sum
            intro p hp
            rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg]
            exact (mul_le_mul_of_nonneg_left (he p hp) vonMangoldt_nonneg).trans_eq (by ring)
       _ ≤ A*(7*(X : ℝ)^(1/200 : ℝ))+E*(M*(1+Real.log X)) := by
            rw [sum_add_distrib,←mul_sum,←mul_sum]
            exact add_le_add (mul_le_mul_of_nonneg_left hmass hA) (mul_le_mul_of_nonneg_left hmert hE)
       _ ≤ _ := by
            let P := ((D+1 : ℕ) : ℝ)^2*(R : ℝ)^3*(X : ℝ)^(99/200 : ℝ)
            let U := ((D+1 : ℕ) : ℝ)*R*Real.sqrt X
            have hP : 0 ≤ P := by dsimp [P]; positivity
            have hU : 0 ≤ U := by dsimp [U]; positivity
            have hp : A*(7*(X : ℝ)^(1/200 : ℝ))=7*C*P*(1+Real.log X) := by
              dsimp [A,P]; rw [←hexp]; ring
            rw [hp]
            change _+E*(M*(1+Real.log X)) ≤ (7*C+B*M)*(P+U)*(1+Real.log X)
            have heq : E=B*U := by dsimp [E,U]; ring
            rw [heq]
            nlinarith only [mul_nonneg (mul_nonneg hB (zero_le_one.trans hM)) (mul_nonneg hP (by positivity : 0 ≤ 1+Real.log X)),
              mul_nonneg hC (mul_nonneg hU (by positivity : 0 ≤ 1+Real.log X))]

/-- Products above the fixed-power first-prime cutoff and outside the
reciprocal band of the complementary factor. -/
def remainingPrimeProducts (D R X : ℕ) : ℝ :=
  let Y := productLower D X
  let Q := ⌊(X : ℝ)^(1/200 : ℝ)⌋₊
  ∑ p ∈ (Ioc (max (2*(D+1)) Q) X).filter Nat.Prime, vonMangoldt p*
    ∑ v ∈ ((Ioc (Y/p) (X/p)).filter (p.Coprime ·)) with
      ¬(v ∈ shortComplement D X ∧ p ∈ reciprocalProductPrimes D X Y v),
      innerJump D v*centeredPrimeWeight R (X/p/v)

/-- A short prime times a short complementary factor lies below the
lower product cutoff. Thus the two deletions are disjoint. -/
theorem short_first_partition {X : ℕ} (hx : 1 ≤ X) (D R : ℕ) :
    outsideReciprocalBand D R X (productLower D X) =
      shortFirstRow D R X (productLower D X)+remainingPrimeProducts D R X := by
  let Q := ⌊(X : ℝ)^(1/200 : ℝ)⌋₊
  let Y := productLower D X
  let S := (Ioc (2*(D+1)) X).filter Nat.Prime
  let clipped (p : ℕ) :=
    ∑ v ∈ ((Ioc (Y/p) (X/p)).filter (p.Coprime ·)) with
      ¬(v ∈ shortComplement D X ∧ p ∈ reciprocalProductPrimes D X Y v),
      innerJump D v*centeredPrimeWeight R (X/p/v)
  have h₁ : S.filter (fun p => p ≤ Q) = shortFirstPrimes D X := by
    ext p
    simp only [S,Q,shortFirstPrimes,mem_filter,mem_Ioc,le_min_iff]; tauto
  have h₂ : S.filter (fun p => ¬p ≤ Q) = (Ioc (max (2*(D+1)) Q) X).filter Nat.Prime := by
    ext p
    simp only [S,mem_filter,mem_Ioc,max_lt_iff,not_le]; tauto
  have lower : ⌊Real.sqrt X⌋₊ ≤ Y := by
    refine le_min (Nat.floor_le_of_le ?_) (Nat.le_mul_of_pos_left _ (Nat.succ_pos D))
    rw [Real.sqrt_eq_rpow]
    exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx) (by norm_num : (1/2 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _)
  have clear (p : ℕ) (hp : p ∈ shortFirstPrimes D X) : clipped p=coprimeSlice D R X Y p := by
    obtain ⟨hh,prime⟩ := mem_filter.mp hp
    have hpQ : p ≤ Q := (mem_Ioc.mp hh).2.trans (min_le_right ..)
    have hp' : (p : ℝ) ≤ (X : ℝ)^(1/200 : ℝ) := (by exact_mod_cast hpQ : (p : ℝ) ≤ Q).trans (Nat.floor_le (by positivity))
    dsimp [clipped,coprimeSlice]
    congr 1
    apply filter_true_of_mem
    intro v hv hpair
    have hvF := (mem_Ioc.mp hpair.1).2
    have hv' : (v : ℝ) ≤ (X : ℝ)^(1/10000 : ℝ) :=
      (by exact_mod_cast hvF : (v : ℝ) ≤ (⌊(X : ℝ)^(1/10000 : ℝ)⌋₊ : ℕ)).trans (Nat.floor_le (by positivity))
    have hprod : v*p ≤ ⌊Real.sqrt X⌋₊ := by
      apply Nat.le_floor
      rw [Nat.cast_mul,Real.sqrt_eq_rpow]
      apply (mul_le_mul hv' hp' (Nat.cast_nonneg p) (by positivity)).trans
      rw [←Real.rpow_add (by exact_mod_cast hx : (0 : ℝ) < X)]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx) (by norm_num)
    have hy := (Nat.div_lt_iff_lt_mul prime.pos).mp (mem_Ioc.mp (mem_filter.mp hv).1).1
    exact (not_lt_of_ge (hprod.trans lower)) hy
  have eq := sum_filter_add_sum_filter_not S (fun p => p ≤ Q) (fun p => vonMangoldt p*clipped p)
  rw [h₁,h₂] at eq
  change (∑ p ∈ S, vonMangoldt p*clipped p) = _+_
  rw [←eq]
  congr 1
  exact sum_congr rfl fun p hp => congrArg (vonMangoldt p*·) (clear p hp)

