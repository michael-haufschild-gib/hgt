import GaloisForLFunctions.HTGeometry.ChronologicalTensor.ProbeComparison
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

/-!
# Finite stabilization under enclosure

Multiplying a window polynomial by powers of net displacement eventually makes
its signed capacity exactly equal to its monotone capacity. The proof gives an
explicit degree/coefficient bound, lifts monotone probes to the unit sphere,
and proves equality of monotone and signed observational kernels by a polynomial
identity argument. No nonzero-response hypothesis is needed.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Finset

def unitMagnitude (t : ℝ) : ℝ := min |t| 1

theorem unitMagnitude_bounds (t : ℝ) : 0 ≤ unitMagnitude t ∧ unitMagnitude t ≤ 1 :=
  ⟨le_min (abs_nonneg _) (by positivity), min_le_right _ _⟩

theorem power_penalty (t : ℝ) (k : ℕ) :
    unitMagnitude t ^ k * (1+(k : ℝ)*(1-unitMagnitude t)) ≤ 1 := by
  let z := unitMagnitude t
  have hz : 0 ≤ z := (unitMagnitude_bounds t).1
  change z^k*(1+(k : ℝ)*(1-z)) ≤ 1
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,Nat.cast_add,Nat.cast_one]
    have hp := mul_nonneg (mul_nonneg (pow_nonneg hz k)
      (show 0 ≤ (k : ℝ)+1 by positivity)) (sq_nonneg (1-z))
    nlinarith

theorem power_penalty_envelope (t M L : ℝ) (k : ℕ) :
    unitMagnitude t ^ (k+1) * (|M|+|L| * (1-unitMagnitude t)) ≤
      max |M| (|L|/(k+1 : ℝ)) := by
  let z := unitMagnitude t
  let C := max |M| (|L|/(k+1 : ℝ))
  have hz0 : 0 ≤ z := (unitMagnitude_bounds t).1
  have hz1 : z ≤ 1 := (unitMagnitude_bounds t).2
  have hC0 : 0 ≤ C := (abs_nonneg M).trans (le_max_left _ _)
  have hMC : |M| ≤ C := le_max_left _ _
  have hLC : |L| ≤ (k+1 : ℝ)*C := by
    have hd : (0 : ℝ) < k+1 := by positivity
    have h := (div_le_iff₀ hd).mp (le_max_right |M| (|L|/(k+1 : ℝ)))
    nlinarith
  have hp := power_penalty t (k+1)
  simp only [Nat.cast_add,Nat.cast_one] at hp
  change z^(k+1)*(|M|+|L| * (1-z)) ≤ C
  calc
    _ ≤ z^(k+1)*(C+((k+1 : ℝ)*C)*(1-z)) :=
      mul_le_mul_of_nonneg_left (add_le_add hMC
        (mul_le_mul_of_nonneg_right hLC (sub_nonneg.mpr hz1))) (pow_nonneg hz0 _)
    _ = C*(z^(k+1)*(1+(k+1 : ℝ)*(1-z))) := by ring
    _ ≤ C*1 := mul_le_mul_of_nonneg_left hp hC0
    _ = C := mul_one _

theorem normalized_displacement_bound {n : ℕ} (g : Fin n → ℝ) :
    |displacement (normalizeProbe g)| ≤ 1 :=
  (abs_sum_le_sum_abs _ _).trans (normalizeProbe_budget g)

def monotoneCapacity {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) : ℝ := sSup (Set.range (fun g => |familyValue D c (monotoneProbe g)|))

def sealedCapacity {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (k : ℕ) : ℝ := sSup (Set.range (fun g =>
      |displacement (normalizeProbe g)^k*familyValue D c (normalizeProbe g)|))

theorem monotone_values_bddAbove {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) : BddAbove (Set.range (fun g => |familyValue D c (monotoneProbe g)|)) := by
  refine ⟨coefficientBudget c, ?_⟩
  rintro _ ⟨g,rfl⟩
  dsimp only
  rw [← normalizeProbe_abs]
  exact normalized_familyValue_bound D c _

theorem monotoneCapacity_probe_bound {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (g : Fin n → ℝ) :
    |familyValue D c (monotoneProbe g)| ≤ monotoneCapacity D c :=
  le_csSup (monotone_values_bddAbove D c) (Set.mem_range_self g)

theorem monotoneCapacity_nonneg {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) : 0 ≤ monotoneCapacity D c :=
  (abs_nonneg _).trans (monotoneCapacity_probe_bound D c (fun _ => 0))

theorem sealed_values_bddAbove {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (k : ℕ) : BddAbove (Set.range (fun g =>
      |displacement (normalizeProbe g)^k*familyValue D c (normalizeProbe g)|)) := by
  refine ⟨coefficientBudget c, ?_⟩
  rintro _ ⟨g,rfl⟩
  dsimp only
  rw [abs_mul,abs_pow]
  have hp := pow_le_pow_left₀ (abs_nonneg _) (normalized_displacement_bound g) k
  rw [one_pow] at hp
  exact (mul_le_mul hp (normalized_familyValue_bound D c g) (abs_nonneg _)
    (by positivity)).trans_eq (one_mul _)

theorem sealedCapacity_probe_bound {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (k : ℕ) (g : Fin n → ℝ) :
    |displacement (normalizeProbe g)^k*familyValue D c (normalizeProbe g)| ≤ sealedCapacity D c k :=
  le_csSup (sealed_values_bddAbove D c k) (Set.mem_range_self g)

theorem sealedCapacity_upper {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (k : ℕ) : sealedCapacity D c (k+1) ≤
      max (monotoneCapacity D c) ((r : ℝ)*coefficientBudget c/(k+1 : ℝ)) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨g,rfl⟩
  dsimp only
  rw [abs_mul,abs_pow]
  have hb := family_reversal_defect D c g
  have hc : 0 ≤ (r : ℝ)*coefficientBudget c := by unfold coefficientBudget; positivity
  have hm := monotoneCapacity_probe_bound D c g
  have hp := power_penalty_envelope (displacement (normalizeProbe g))
    (monotoneCapacity D c) ((r : ℝ)*coefficientBudget c) k
  rw [abs_of_nonneg (monotoneCapacity_nonneg D c),abs_of_nonneg hc,
    unitMagnitude,min_eq_left (normalized_displacement_bound g)] at hp
  exact (mul_le_mul_of_nonneg_left
    (hb.trans (add_le_add hm le_rfl)) (pow_nonneg (abs_nonneg _) _)).trans hp


theorem variation_eq_zero_iff {n : ℕ} (g : Fin n → ℝ) : variation g = 0 ↔ g = 0 := by
  constructor
  · intro h
    funext i
    have hb := windowValue_bound {i} g
    simp only [windowValue,sum_singleton,h] at hb
    exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
  · rintro rfl
    simp [variation]

def radialProbe {n : ℕ} (g : Fin (n+1) → ℝ) : Fin (n+1) → ℝ :=
  if variation g = 0 then fun i => if i = 0 then 1 else 0
  else fun i => |g i| / variation g

theorem radialProbe_data {n : ℕ} (g : Fin (n+1) → ℝ) :
    (∀ i, 0 ≤ radialProbe g i) ∧ displacement (radialProbe g) = 1 ∧
      (fun i => |g i|) = fun i => variation g * radialProbe g i := by
  by_cases hv : variation g = 0
  · have hg := (variation_eq_zero_iff g).mp hv
    subst g
    simp [radialProbe,variation,displacement]
    intro i
    split_ifs <;> positivity
  · have hp : 0 < variation g := lt_of_le_of_ne (variation_nonneg g) (Ne.symm hv)
    simp only [radialProbe,if_neg hv]
    refine ⟨fun i => div_nonneg (abs_nonneg _) hp.le, ?_, ?_⟩
    · simp only [displacement,← sum_div]
      exact div_self hv
    · funext i
      field_simp

theorem radialProbe_variation {n : ℕ} (g : Fin (n+1) → ℝ) : variation (radialProbe g) = 1 := by
  have h := radialProbe_data g
  simpa only [variation,displacement,abs_of_nonneg (h.1 _)] using h.2.1

theorem familyValue_scale {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (g : Fin n → ℝ) (t : ℝ) :
    familyValue D c (fun i => t*g i) = t^r*familyValue D c g := by
  simp only [familyValue,diagramValue,windowValue,← mul_sum,prod_mul_distrib,prod_const,
    card_univ,Fintype.card_fin]
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  ring

theorem monotoneCapacity_le_sealed {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) (k : ℕ) : monotoneCapacity D c ≤ sealedCapacity D c k := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨g,rfl⟩
  dsimp only
  let h := radialProbe (normalizeProbe g)
  have hh : variation h = 1 := radialProbe_variation _
  have hf : normalizeProbe h = h := (normalizeProbe_fixed_iff h).mpr (le_of_eq hh)
  have hd : displacement h = 1 := (radialProbe_data _).2.1
  have he : monotoneProbe g = fun i => variation (normalizeProbe g)*h i := (radialProbe_data _).2.2
  have hb := sealedCapacity_probe_bound D c k h
  rw [hf,hd,one_pow,one_mul] at hb
  rw [he,familyValue_scale,abs_mul,abs_pow,abs_of_nonneg (variation_nonneg _)]
  have hp := pow_le_pow_left₀ (variation_nonneg _) (normalizeProbe_budget g) r
  rw [one_pow] at hp
  exact ((mul_le_mul_of_nonneg_right hp (abs_nonneg _)).trans_eq (one_mul _)).trans hb


theorem familyValue_abs_scale {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (g : Fin n → ℝ) :
    familyValue D c (fun i => |g i|) =
      max 1 (variation g)^r*familyValue D c (monotoneProbe g) := by
  have hd : 0 < max 1 (variation g) := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have he : (fun i => |g i|) = fun i => max 1 (variation g)*monotoneProbe g i := by
    funext i
    simp only [monotoneProbe,normalizeProbe,abs_div,abs_of_pos hd]
    field_simp
  rw [he,familyValue_scale]

def probeLinePolynomial {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (g : Fin n → ℝ) : Polynomial ℝ :=
  ∑ j, Polynomial.C (c j)*∏ k, ∑ i ∈ D j k,
    (Polynomial.C |g i| + Polynomial.X*Polynomial.C (g i-|g i|))

theorem probeLinePolynomial_eval {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (g : Fin n → ℝ) (t : ℝ) :
    (probeLinePolynomial D c g).eval t = familyValue D c (fun i => |g i|+t*(g i-|g i|)) := by
  simp only [probeLinePolynomial,familyValue,diagramValue,windowValue,
    Polynomial.eval_finsetSum,Polynomial.eval_prod,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_C,Polynomial.eval_X]

theorem monotoneCapacity_zero_iff {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) : monotoneCapacity D c = 0 ↔ familyCapacity D c = 0 := by
  constructor
  · intro hm
    have hzero (g : Fin n → ℝ) : familyValue D c (fun i => |g i|) = 0 := by
      have h := monotoneCapacity_probe_bound D c g
      rw [hm] at h
      have hz := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
      rw [familyValue_abs_scale,hz,mul_zero]
    apply (familyCapacity_zero_iff D c).mpr
    intro g
    let h := normalizeProbe g
    have hq : probeLinePolynomial D c h = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      have hi : (Set.Icc (0 : ℝ) (1/2)).Infinite := Set.Icc_infinite (by positivity)
      apply hi.mono
      intro t ht
      change (probeLinePolynomial D c h).eval t = 0
      rw [probeLinePolynomial_eval]
      have hn (i : Fin n) : 0 ≤ |h i|+t*(h i-|h i|) := by
        by_cases hs : 0 ≤ h i
        · rw [abs_of_nonneg hs]
          simpa using hs
        · rw [abs_of_neg (lt_of_not_ge hs)]
          nlinarith [ht.2]
      simpa only [abs_of_nonneg (hn _)] using hzero (fun i => |h i|+t*(h i-|h i|))
    have he := congrArg (Polynomial.eval 1) hq
    rw [probeLinePolynomial_eval] at he
    simpa using he
  · intro hf
    apply le_antisymm _ (monotoneCapacity_nonneg D c)
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨g,rfl⟩
    dsimp only
    rw [← normalizeProbe_abs,(familyCapacity_zero_iff D c).mp hf,abs_zero]

theorem sealedCapacity_of_zero {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (k : ℕ) :
    monotoneCapacity D c = 0 ↔ sealedCapacity D c k = 0 ∧ familyCapacity D c = 0 := by
  constructor
  · intro hm
    have hf := (monotoneCapacity_zero_iff D c).mp hm
    refine ⟨?_,hf⟩
    have he : (fun g => |displacement (normalizeProbe g)^k*familyValue D c (normalizeProbe g)|) =
        fun (_ : Fin n → ℝ) => (0 : ℝ) := by
      funext g
      rw [(familyCapacity_zero_iff D c).mp hf,mul_zero,abs_zero]
    simp only [sealedCapacity,he,Set.range_const,csSup_singleton]
  · intro h
    exact (monotoneCapacity_zero_iff D c).mpr h.2

theorem eventual_exact_sealing {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) : ∃ k₀ : ℕ, ∀ k : ℕ,
      sealedCapacity D c (k₀+k) = monotoneCapacity D c := by
  by_cases hm : monotoneCapacity D c = 0
  · refine ⟨0,fun k => ?_⟩
    rw [hm]
    exact ((sealedCapacity_of_zero D c (0+k)).mp hm).1
  · have hp : 0 < monotoneCapacity D c :=
      lt_of_le_of_ne (monotoneCapacity_nonneg D c) (Ne.symm hm)
    obtain ⟨N,hN⟩ := exists_nat_ge ((r : ℝ)*coefficientBudget c/monotoneCapacity D c)
    refine ⟨N+1,fun k => le_antisymm ?_ (monotoneCapacity_le_sealed D c (N+1+k))⟩
    have hbound := sealedCapacity_upper D c (N+k)
    have he : N+k+1 = N+1+k := by omega
    rw [he] at hbound
    apply hbound.trans
    apply max_le le_rfl
    have hd : (0 : ℝ) < N+k+1 := by positivity
    rw [Nat.cast_add]
    apply (div_le_iff₀ hd).mpr
    have hNN := (div_le_iff₀ hp).mp hN
    nlinarith

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
