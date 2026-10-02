import GaloisForLFunctions.RHTower.MobiusDivisorFiniteClockCountingCancellation
import GaloisForLFunctions.RHTower.SqrtTelescopeSums

/-!+# A cardinality bound for the complete finite clock defect

Splitting the actual squarefree cofactors at `M / 4^card(P)` bounds the
excess logarithmic age by `4*M^2`. The remaining age is charged to the
actual energy with coefficient `card(P)*log 4`. The comparison is uniform
in the processed prime core and cutoff; it uses no density limit.
-/

noncomputable section
open Finset
namespace RHTower

private lemma logarithmic_count_real {X : ℝ} (hX : 0 < X) (N : ℕ)
    (hNX : (N : ℝ) ≤ X) :
    (∑ r ∈ Icc 1 N, (Real.log X - Real.log r)) ≤ 4*X := by
  calc
    _ ≤ ∑ r ∈ Icc 1 N, (2*Real.sqrt X)*(1/Real.sqrt r) := by
      apply sum_le_sum
      intro r hr
      have hrR : (0 : ℝ) < r := by exact_mod_cast (mem_Icc.mp hr).1
      have hx : 0 < X/r := div_pos hX hrR
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
      rw [Real.log_sqrt hx.le, Real.log_div hX.ne' hrR.ne',
        Real.sqrt_div hX.le] at h
      simp only [div_eq_mul_inv, one_mul] at h ⊢
      linarith
    _ = 2*Real.sqrt X * ∑ r ∈ Icc 1 N, 1/Real.sqrt r := by rw [mul_sum]
    _ ≤ 2*Real.sqrt X*(2*Real.sqrt N) :=
      mul_le_mul_of_nonneg_left (sum_inv_sqrt_le N) (by positivity)
    _ ≤ 2*Real.sqrt X*(2*Real.sqrt X) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hNX) (by positivity))
        (by positivity)
    _ = _ := by nlinarith only [Real.sq_sqrt hX.le]

private lemma finite_clock_truncation (M B : ℕ) (hB : 0 < B)
    (S : Finset ℕ) (hS : S ⊆ Icc 1 M) (v : ℕ → ℝ)
    (hv : ∀ r ∈ S, 0 ≤ v r) (hcap : ∀ r ∈ S, v r ≤ (B : ℝ)*M) :
    (∑ r ∈ S, (Real.log M-Real.log r)*v r) ≤
      Real.log B*(∑ r ∈ S, v r)+4*(M : ℝ)^2 := by
  classical
  rcases M.eq_zero_or_pos with rfl | hM
  · have he : S = ∅ := by simpa using hS
    simp [he]
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  let X : ℝ := (M : ℝ)/B
  let N : ℕ := M/B
  let T := S.filter (fun r => r ≤ N)
  have hX : 0 < X := div_pos hMR hBR
  have hNX : (N : ℝ) ≤ X := by
    apply (le_div_iff₀ hBR).mpr
    exact_mod_cast Nat.div_mul_le_self M B
  have hlogX : Real.log X = Real.log M-Real.log B := Real.log_div hMR.ne' hBR.ne'
  have hg (r : ℕ) (hr : r ∈ Icc 1 N) : 0 ≤ Real.log X-Real.log r := by
    obtain ⟨hr, hrN⟩ := mem_Icc.mp hr
    exact sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hr)
      ((by exact_mod_cast hrN : (r : ℝ) ≤ N).trans hNX))
  have hpoint (r : ℕ) (hr : r ∈ S) :
      (Real.log M-Real.log r)*v r ≤ Real.log B*v r+
        if r ≤ N then ((B : ℝ)*M)*(Real.log X-Real.log r) else 0 := by
    have hr0 := (mem_Icc.mp (hS hr)).1
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
    by_cases hrN : r ≤ N
    · rw [if_pos hrN]
      have hm := mul_le_mul_of_nonneg_left (hcap r hr)
        (hg r (mem_Icc.mpr ⟨hr0, hrN⟩))
      rw [hlogX] at hm ⊢
      nlinarith only [hm]
    · rw [if_neg hrN, add_zero]
      have hMr : M < r*B := (Nat.div_lt_iff_lt_mul hB).mp (lt_of_not_ge hrN)
      have hle : (M : ℝ) ≤ (B : ℝ)*r := by
        exact_mod_cast (show M ≤ B*r by simpa only [Nat.mul_comm] using hMr.le)
      have hl := Real.log_le_log hMR hle
      rw [Real.log_mul hBR.ne' hrR.ne'] at hl
      exact mul_le_mul_of_nonneg_right (by linarith only [hl]) (hv r hr)
  have hT : T ⊆ Icc 1 N := by
    intro r hr
    obtain ⟨hr, hrN⟩ := mem_filter.mp hr
    exact mem_Icc.mpr ⟨(mem_Icc.mp (hS hr)).1, hrN⟩
  calc
    _ ≤ ∑ r ∈ S, (Real.log B*v r+
        if r ≤ N then ((B : ℝ)*M)*(Real.log X-Real.log r) else 0) := sum_le_sum hpoint
    _ = Real.log B*(∑ r ∈ S, v r)+
        ((B : ℝ)*M)*(∑ r ∈ T, (Real.log X-Real.log r)) := by
      rw [sum_add_distrib, ← mul_sum, ← sum_filter]
      rw [← mul_sum]
    _ ≤ Real.log B*(∑ r ∈ S, v r)+
        ((B : ℝ)*M)*(∑ r ∈ Icc 1 N, (Real.log X-Real.log r)) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum_of_subset_of_nonneg hT (fun r hr _ => hg r hr)
    _ ≤ Real.log B*(∑ r ∈ S, v r)+((B : ℝ)*M)*(4*X) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (logarithmic_count_real hX N hNX) (by positivity))
    _ = _ := by dsimp [X]; field_simp

private lemma source_term_bound_pow (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (M : ℕ) {r : ℕ} (hr : r ∈ fixedCoreSquarefreeIndices P M) :
    (r : ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^2 ≤ (4 : ℝ)^P.card*M := by
  obtain ⟨_, hsf, hd⟩ := mem_filter.mp hr
  have he := mobiusDivisorSelectionFibre_product_interpolation M P r.primeFactors
    (fun p hp => (Nat.mem_primeFactors.mp hp).1) hd
  rw [Nat.prod_primeFactors_of_squarefree hsf] at he
  have hm : (((ArithmeticFunction.moebius r : ℤ) : ℝ))^2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
  have hs := congrArg (fun x : ℝ => x^2) he
  simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg r), hm, mul_one] at hs
  rw [← hs]
  have ha := abs_mobiusDivisorSelectionFibre_le_source_amplitude M P r.primeFactors hP
    (fun p hp => (Nat.mem_primeFactors.mp hp).1)
  have hp : (2 : ℝ)^(P.card-1) ≤ (2 : ℝ)^P.card :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hc : (3/5 : ℝ)*2^(P.card-1) ≤ (2 : ℝ)^P.card := by
    have hn : (0 : ℝ) ≤ 2^(P.card-1) := by positivity
    linarith only [hp, hn]
  have hb := ha.trans (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg M))
  have hh : (mobiusDivisorSelectionFibre M P r.primeFactors)^2 ≤
      ((2 : ℝ)^P.card*Real.sqrt M)^2 := by
    nlinarith only [hb, abs_nonneg (mobiusDivisorSelectionFibre M P r.primeFactors),
      sq_abs (mobiusDivisorSelectionFibre M P r.primeFactors),
      sq_nonneg ((2 : ℝ)^P.card*Real.sqrt M-
        |mobiusDivisorSelectionFibre M P r.primeFactors|)]
  have hpow : ((2 : ℝ)^P.card)^2 = (4 : ℝ)^P.card := by
    rw [← pow_mul, Nat.mul_comm P.card 2, pow_mul]
    norm_num
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg M), hpow] using hh

private lemma clock_cardinality_nat (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (M : ℕ) :
    (1+Real.log M-(P.card : ℝ)*Real.log 4)*mobiusDivisorSelectionEnergy M P ≤
      mobiusDivisorFiniteClockEnergy 1 M P+4*(M : ℝ)^2 := by
  let S := fixedCoreSquarefreeIndices P M
  let v := fun r : ℕ => (r : ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^2
  have h := finite_clock_truncation M (4^P.card) (by positivity) S
    (filter_subset _ _) v (fun r _ => by dsimp [v]; positivity) (by
      intro r hr
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using source_term_bound_pow P hP M hr)
  have he : (1+Real.log M)*mobiusDivisorSelectionEnergy M P-
      mobiusDivisorFiniteClockEnergy 1 M P =
      ∑ r ∈ S, (Real.log M-Real.log r)*v r := by
    rw [mobiusDivisorSelectionEnergy_eq_inclusive_squarefree, mobiusDivisorFiniteClockEnergy,
      mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro r _
    dsimp [v]
    ring
  have hsum : (∑ r ∈ S, v r) = mobiusDivisorSelectionEnergy M P :=
    (mobiusDivisorSelectionEnergy_eq_inclusive_squarefree P M).symm
  rw [hsum, ← he, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
  nlinarith only [h]

/-- The full finite logarithmic clock defect costs only a linear multiple
of core cardinality times the actual energy, plus a universal quadratic
remainder. Every processed core consists of literal primes. -/
theorem mobiusDivisorFiniteClockEnergy_cardinality_bound :
    ∀ (P : Finset Nat.Primes) (M : ℕ),
      let Q := P.image (fun p : Nat.Primes => (p : ℕ))
      (1+Real.log M-(P.card : ℝ)*Real.log 4)*mobiusDivisorSelectionEnergy M Q ≤
        mobiusDivisorFiniteClockEnergy 1 M Q+4*(M : ℝ)^2 := by
  intro P M
  dsimp only
  have hP : ∀ p ∈ P.image (fun p : Nat.Primes => (p : ℕ)), p.Prime := by
    intro p hp
    obtain ⟨q, _, rfl⟩ := mem_image.mp hp
    exact q.property
  have h := clock_cardinality_nat _ hP M
  have hc : (P.image (fun p : Nat.Primes => (p : ℕ))).card = P.card :=
    card_image_of_injective P (fun _ _ h => Subtype.ext h)
  rw [hc] at h
  exact h

end RHTower
