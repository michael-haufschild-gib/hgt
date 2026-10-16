import GaloisForLFunctions.HTGeometry.OrderOneConvergenceExponent
import GaloisForLFunctions.HTGeometry.CanonicalProductGrowth

/-!
# Subquadratic type of products selected from order-one divisors

Every inverse power with exponent greater than one is summable. Consequently
any selected genus-one product has growth of order strictly below two, the
growth condition used to recover exponential type from bounds on both axes.
-/

open Filter Topology Set
noncomputable section
namespace GaloisForLFunctions.CountableDivisor

private theorem summable_exp_neg_nat {a : ℝ} (ha : 0<a) :
    Summable fun n : ℕ => Real.exp (-a*n) := by
  have h := summable_geometric_of_norm_lt_one (show ‖Real.exp (-a)‖<1 by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith))
  apply h.congr
  intro n
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem summable_orderOneBucketMajorant_rpow {K p : ℝ} (hK : 0≤K) (hp : 1<p) :
    Summable fun n : ℕ =>
      (K*(1+Real.exp (n+1))*Real.log (2+Real.exp (n+1)))*Real.exp (-p*n) := by
  have ha : 0<p-1 := by linarith
  have hm : Summable fun n : ℕ =>
      (2*K*Real.exp 1)*(((n:ℝ)+1)*Real.exp (-(p-1)*n))+
        (2*K*Real.exp 1*Real.log 2)*Real.exp (-(p-1)*n) :=
    ((summable_linear_expNeg ha).mul_left _).add ((summable_exp_neg_nat ha).mul_left _)
  apply hm.of_nonneg_of_le
  · intro n
    have hl : 0≤Real.log (2+Real.exp ((n:ℝ)+1)) :=
      Real.log_nonneg (by have := Real.exp_pos ((n:ℝ)+1); linarith)
    positivity
  intro n
  set E := Real.exp ((n:ℝ)+1) with hE
  have hE1 : 1≤E := Real.one_le_exp (by positivity)
  have hE2 : 2≤E := by
    have hh := Real.add_one_le_exp (1:ℝ)
    have hh' : Real.exp 1≤E := Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  have hl : Real.log (2+E)≤Real.log 2+((n:ℝ)+1) := by
    calc
      Real.log (2+E)≤Real.log (2*E) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2+((n:ℝ)+1) := by
        rw [Real.log_mul (by norm_num) (by positivity),hE,Real.log_exp]
  have hl0 : 0≤Real.log (2+E) := Real.log_nonneg (by linarith)
  have hEe : E*Real.exp (-p*(n:ℝ))=Real.exp 1*Real.exp (-(p-1)*n) := by
    rw [hE,← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  calc
    K*(1+E)*Real.log (2+E)*Real.exp (-p*(n:ℝ)) ≤
        K*(2*E)*(Real.log 2+((n:ℝ)+1))*Real.exp (-p*n) := by
      gcongr
      · linarith
    _ = _ := by
      calc
        _ = 2*K*(Real.log 2+((n:ℝ)+1))*(E*Real.exp (-p*n)) := by ring
        _ = _ := by rw [hEe]; ring

theorem summable_rpow_neg_of_orderOneDensity {ι : Type*} {a : ι → ℂ}
    (hloc : LocallyFiniteDivisor a) (hden : OrderOneDensityIdx a) {p : ℝ} (hp : 1<p) :
    Summable fun i => ‖a i‖^(-p) := by
  classical
  obtain ⟨K,hK,hcount⟩ := hden
  let S : Set ι := {i | ‖a i‖≤1}
  rw [← summable_subtype_and_compl (s := S)]
  constructor
  · haveI : Finite S := (hloc 1).to_subtype
    exact Summable.of_finite
  have hgt (q : ↑(Sᶜ)) : 1<‖a q.1‖ := by simpa only [S,mem_compl_iff,mem_setOf_eq,not_le] using q.2
  have hle (n : ℕ) : {q : ↑(Sᶜ) | logBucket a q.1=n}.ncard≤{i : ι | logBucket a i=n}.ncard :=
    Set.ncard_le_ncard_of_injOn (fun q : ↑(Sᶜ) => q.1) (fun _ h => h)
      (fun _ _ _ _ h => Subtype.ext h) (finite_logBucket_fiber hloc n)
  have hfib (n : ℕ) : {q : ↑(Sᶜ) | logBucket a q.1=n}.Finite := by
    apply Set.Finite.of_finite_image (f := Subtype.val)
    · exact (finite_logBucket_fiber hloc n).subset (by rintro _ ⟨q,hq,rfl⟩; exact hq)
    · exact Subtype.val_injective.injOn
  refine summable_of_bucket _ (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (fun q => logBucket a q.1) hfib (fun n => Real.exp (-p*n))
    (fun q => norm_rpow_le_expBucket (hgt q) (by linarith)) ?_
  apply (summable_orderOneBucketMajorant_rpow hK hp).of_nonneg_of_le
  · intro n
    positivity
  intro n
  have hc : ({q : ↑(Sᶜ) | logBucket a q.1=n}.ncard:ℝ)≤
      (divisorIdxCount a (Real.exp ((n:ℝ)+1)):ℝ) :=
    (show ({q : ↑(Sᶜ) | logBucket a q.1=n}.ncard:ℝ)≤
      ({i : ι | logBucket a i=n}.ncard:ℝ) by exact_mod_cast hle n).trans
        (ncard_logBucket_fiber_le hloc n)
  exact mul_le_mul_of_nonneg_right
    (hc.trans (hcount _ (Real.one_le_exp (by positivity)))) (Real.exp_nonneg _)

end GaloisForLFunctions.CountableDivisor

namespace RHTower

theorem min_linear_quadratic_le_rpow {x p : ℝ} (hx : 0≤x) (hp1 : 1≤p) (hp2 : p≤2) :
    min x (x^2)≤x^p := by
  by_cases h1 : 1≤x
  · apply (min_le_left _ _).trans
    simpa using Real.rpow_le_rpow_of_exponent_le h1 hp1
  apply (min_le_right _ _).trans
  simpa only [Real.rpow_two] using
    Real.rpow_le_rpow_of_exponent_ge' hx (le_of_not_ge h1) (by linarith) hp2

theorem canonicalProduct_norm_le_exp_rpow {ι : Type*} (a : ι → ℂ)
    (ha : ∀ i,a i≠0) (hs : Summable fun i => 1/‖a i‖^2)
    {p : ℝ} (hp1 : 1≤p) (hp2 : p≤2) (hsp : Summable fun i => ‖a i‖^(-p)) (z : ℂ) :
    ‖canonicalProductE1Indexed a z‖≤Real.exp ((2*∑' i,‖a i‖^(-p))*‖z‖^p) := by
  apply (canonicalProductE1Indexed_norm_le_exp_min a ha hs z).trans
  apply Real.exp_le_exp.mpr
  have hpoint (i : ι) :
      min (2*‖z‖/‖a i‖) (2*‖z‖^2/‖a i‖^2)≤(2*‖z‖^p)*‖a i‖^(-p) := by
    have hh := mul_le_mul_of_nonneg_left
      (min_linear_quadratic_le_rpow (div_nonneg (norm_nonneg z) (norm_nonneg (a i))) hp1 hp2)
      (show (0:ℝ)≤2 by norm_num)
    rw [mul_min_of_nonneg _ _ (by norm_num),div_pow,
      Real.div_rpow (norm_nonneg z) (norm_nonneg (a i)) p] at hh
    rw [Real.rpow_neg (norm_nonneg _)]
    simpa only [div_eq_mul_inv,mul_assoc] using hh
  have hmaj := hsp.mul_left (2*‖z‖^p)
  have hmin := hmaj.of_nonneg_of_le (fun _ => le_min (by positivity) (by positivity)) hpoint
  calc
    _ ≤ ∑' i,(2*‖z‖^p)*‖a i‖^(-p) := hmin.tsum_le_tsum hpoint hmaj
    _ = _ := by rw [tsum_mul_left]; ring

end RHTower
