import GaloisForLFunctions.RHTower.ChebyshevErrorExponentLaw
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsZeroFreeHalfPlane
import GaloisForLFunctions.HTGeometry.DiscreteAbelRing

/-!
# Prime intervals on the rescaled conductor

At x = t sqrt(q), each floor-free power cutoff x^α < q becomes a lower
cut on q^(1-α/2). Both conductor endpoints and both product cutoffs
therefore leave a single interval on each slice. Partial summation on that
interval retains the ordinary signed Mangoldt measure.
-/

noncomputable section
open Finset ArithmeticFunction
open _root_.RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem scaled_power_identity {t q : ℝ} (ht : 0 ≤ t) (hq : 0 < q) (α : ℝ) :
    (t * Real.sqrt q)^α = t^α * q^(α/2) := by
  rw [Real.mul_rpow ht (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul hq.le]
  congr 2
  ring

/-- Normalized shell after x = t sqrt(q). The two exponents may differ, so the
same interval description applies between two distinct power cutoffs. -/
theorem rescaled_product_conditions {t q c : ℝ} (ht : 0 ≤ t) (hq : 0 < q) (α β : ℝ) :
    ((t*Real.sqrt q)^α < q ∧ q ≤ c*(t*Real.sqrt q)^β) ↔
      (t^α < q^(1-α/2) ∧ q^(1-β/2) ≤ c*t^β) := by
  rw [scaled_power_identity ht hq α, scaled_power_identity ht hq β]
  have hdiv (a : ℝ) : q^(1-a/2) = q / q^(a/2) := by
    rw [Real.rpow_sub hq, Real.rpow_one]
  rw [hdiv, hdiv, lt_div_iff₀ (Real.rpow_pos_of_pos hq _),
    div_le_iff₀ (Real.rpow_pos_of_pos hq _), mul_assoc]

/-- All products in one rescaled conductor slice, truncated to positive products at most H. -/
def rescaledShellProducts (H : ℕ) (L U t α β c : ℝ) : Finset ℕ :=
  (Icc 1 H).filter fun q => L < t*Real.sqrt q ∧ t*Real.sqrt q ≤ U ∧
    (t*Real.sqrt q)^α < (q:ℝ) ∧ (q:ℝ) ≤ c*(t*Real.sqrt q)^β

/-- Both shell boundaries and a partial conductor octave survive as one interval. -/
theorem rescaledShellProducts_interval (H : ℕ) (L U c : ℝ) {t α β : ℝ}
    (ht : 0 ≤ t) (ha : α ≤ 2) (hb : β ≤ 2) :
    ∃ l u : ℕ, l ≤ u ∧ u ≤ H ∧ rescaledShellProducts H L U t α β c = Ioc l u := by
  let S := rescaledShellProducts H L U t α β c
  by_cases hh : S.Nonempty
  · let a := S.min' hh
    let b := S.max' hh
    have has : a ∈ S := min'_mem S hh
    have hbs : b ∈ S := max'_mem S hh
    obtain ⟨hai,haL,_,hac⟩ := mem_filter.mp has
    obtain ⟨hbi,_,hbU,hbc⟩ := mem_filter.mp hbs
    have ha0 := (mem_Icc.mp hai).1
    have hb0 := (mem_Icc.mp hbi).1
    have hab : a ≤ b := le_max' S a has
    have ha' := (rescaled_product_conditions (c := c) ht (Nat.cast_pos.mpr ha0) α β).mp hac
    have hb' := (rescaled_product_conditions (c := c) ht (Nat.cast_pos.mpr hb0) α β).mp hbc
    refine ⟨a-1,b,by omega,(mem_Icc.mp hbi).2,?_⟩
    ext q
    constructor
    · intro hq
      have hl := min'_le S q hq
      exact mem_Ioc.mpr ⟨by omega,le_max' S q hq⟩
    · intro hq
      obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hq
      have haq : a ≤ q := by omega
      have hqa : (a:ℝ) ≤ q := Nat.cast_le.mpr haq
      have hqb : (q:ℝ) ≤ b := Nat.cast_le.mpr hhi
      have hq0 : (0:ℝ) < q := Nat.cast_pos.mpr (ha0.trans haq)
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨ha0.trans haq,hhi.trans (mem_Icc.mp hbi).2⟩,
        haL.trans_le (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hqa) ht),
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hqb) ht).trans hbU,
        (rescaled_product_conditions ht hq0 α β).mpr ⟨?_,?_⟩⟩
      · exact ha'.1.trans_le (Real.rpow_le_rpow (Nat.cast_nonneg _) hqa (by linarith))
      · exact (Real.rpow_le_rpow hq0.le hqb (by linarith)).trans hb'.2
  · exact ⟨0,0,le_rfl,Nat.zero_le H,by simpa only [Ioc_self] using not_nonempty_iff_eq_empty.mp hh⟩

private theorem prime_eight_ninths :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, 1 ≤ T →
      |∑ q ∈ Icc 1 T, (vonMangoldt q-1)| ≤ C*(T:ℝ)^(8/9:ℝ) := by
  have hΘ : zeroReSup ≤ 20999/24000 := zeroReSup_le_of_forall_re_le fun q => by
    by_contra! hq
    exact GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re hq
      (riemannZeta_eq_zero_of_xiZeroCopy q)
  obtain ⟨C,hC,h⟩ := exists_abs_chebyshevPsi_sub_le_rpow
    (show zeroReSup < 8/9 by linarith only [hΘ])
  refine ⟨C,hC,fun T hT => ?_⟩
  have he : (∑ q ∈ Icc 1 T, vonMangoldt q) = Chebyshev.psi T := by
    unfold Chebyshev.psi; rw [Nat.floor_natCast]; rfl
  rw [sum_sub_distrib,he,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_one]
  exact h T (by exact_mod_cast hT)

/-- The Jacobian of the conductor substitution contributes a factor q. The
ordinary prime estimate holds uniformly on every resulting terminal interval. -/
theorem rescaledShellProducts_prime_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℕ, 1 ≤ H → ∀ L U c : ℝ, ∀ {t α β : ℝ},
      0 ≤ t → α ≤ 2 → β ≤ 2 →
      |∑ q ∈ rescaledShellProducts H L U t α β c, (vonMangoldt q-1)*q| ≤
        C*(H:ℝ)^(1+(8/9:ℝ)) := by
  obtain ⟨A,hA,ha⟩ := prime_eight_ninths
  let f := fun q : ℕ => vonMangoldt q-1
  refine ⟨6*A,by positivity,fun H hH L U c t α β ht hα hβ => ?_⟩
  obtain ⟨l,u,hlu,hu,he⟩ := rescaledShellProducts_interval H L U c ht hα hβ
  let B := A*(H:ℝ)^(8/9:ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hH' : 1 ≤ (H:ℝ) := by exact_mod_cast hH
  have pref (m : ℕ) (hm : m ≤ H) : |∑ q ∈ Icc 1 m, f q| ≤ B := by
    rcases Nat.eq_zero_or_pos m with rfl | hm'
    · simpa using hB
    · exact (ha m hm').trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hm) (by norm_num)) hA)
  have weighted (m : ℕ) (hm : m ≤ H) : |∑ q ∈ Icc 1 m, f q * q| ≤ 3*H*B := by
    rw [_root_.HTGeometry.sum_mul_eq_partial_mul_diff_ring f (fun q : ℕ => (q:ℝ))]
    apply (abs_add_le _ _).trans
    have hsum : |∑ q ∈ Icc 1 m, (∑ v ∈ Icc 1 q, f v) * ((q:ℝ) - ((q+1:ℕ):ℝ))| ≤ m*B := by
      apply (abs_sum_le_sum_abs _ _).trans
      calc _ ≤ ∑ _q ∈ Icc 1 m, B := by
              apply sum_le_sum; intro q hq
              simpa [abs_mul] using pref q ((mem_Icc.mp hq).2.trans hm)
           _ = _ := by rw [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
    have hend := mul_le_mul_of_nonneg_right (pref m hm) (Nat.cast_nonneg (α := ℝ) (m+1))
    have hmm := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hm : (m:ℝ) ≤ H) hB
    have hhb := le_mul_of_one_le_left hB hH'
    have ht : |(∑ q ∈ Icc 1 m, f q)*((m+1:ℕ):ℝ)| ≤ B*((m+1:ℕ):ℝ) := by
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg (m+1) : (0:ℝ) ≤ (m+1:ℕ))]
      exact hend
    apply (add_le_add hsum ht).trans
    push_cast
    linarith only [hmm,hhb]
  have hi (k : ℕ) : Ioc 0 k = Icc 1 k := by ext q; simp only [mem_Ioc,mem_Icc]; omega
  have hs := sum_Ioc_consecutive (fun q : ℕ => f q*q) (Nat.zero_le l) hlu
  rw [hi,hi] at hs
  rw [he]
  change |∑ q ∈ Ioc l u, f q*q| ≤ _
  rw [show (∑ q ∈ Ioc l u, f q*q) = (∑ q ∈ Icc 1 u, f q*q)-(∑ q ∈ Icc 1 l, f q*q) by linarith only [hs]]
  apply (abs_sub _ _).trans ((add_le_add (weighted u hu) (weighted l (hlu.trans hu))).trans_eq _)
  dsimp [B]
  rw [Real.rpow_add (zero_lt_one.trans_le hH'),Real.rpow_one]
  ring

/-- A dyadic product cut can be imposed after the conductor rescaling.
All constants remain uniform in its lower endpoint. -/
theorem rescaledShellProducts_band_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℕ, 1 ≤ H → ∀ Q ≤ H, ∀ L U c : ℝ, ∀ {t α β : ℝ},
      0 ≤ t → α ≤ 2 → β ≤ 2 →
      |∑ q ∈ rescaledShellProducts H L U t α β c with Q < q, (vonMangoldt q-1)*q| ≤
        C*(H:ℝ)^(1+(8/9:ℝ)) := by
  obtain ⟨A,hA,ha⟩ := rescaledShellProducts_prime_mass
  refine ⟨A+A,add_nonneg hA hA,fun H hH Q hQ L U c t α β ht hα hβ => ?_⟩
  let S := fun k => rescaledShellProducts k L U t α β c
  let f := fun q : ℕ => (vonMangoldt q-1)*q
  have hsub : S Q ⊆ S H := by
    intro q hq
    exact mem_filter.mpr ⟨Icc_subset_Icc_right hQ (mem_filter.mp hq).1,(mem_filter.mp hq).2⟩
  have eqS : (S H).filter (Q < ·) = S H \ S Q := by
    ext q
    rw [mem_filter,mem_sdiff]
    constructor
    · rintro ⟨hs,hq⟩
      exact ⟨hs,fun h => hq.not_ge (mem_Icc.mp (mem_filter.mp h).1).2⟩
    · rintro ⟨hs,hn⟩
      refine ⟨hs,lt_of_not_ge fun hq => hn ?_⟩
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hs).1).1,hq⟩,(mem_filter.mp hs).2⟩
  have hsplit := sum_sdiff (f := f) hsub
  change |∑ q ∈ (S H).filter (Q < ·), f q| ≤ _
  rw [eqS,show (∑ q ∈ S H \ S Q, f q) = (∑ q ∈ S H, f q)-(∑ q ∈ S Q, f q) by linarith only [hsplit]]
  apply (abs_sub _ _).trans
  have hleft := ha H hH L U c ht hα hβ
  have hright : |∑ q ∈ S Q, f q| ≤ A*(H:ℝ)^(1+(8/9:ℝ)) := by
    rcases Nat.eq_zero_or_pos Q with rfl | hpos
    · simp only [S,rescaledShellProducts,Icc_eq_empty_of_lt Nat.zero_lt_one,filter_empty,sum_empty,abs_zero]
      positivity
    · exact (ha Q hpos L U c ht hα hβ).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hQ) (by norm_num)) hA)
  rw [add_mul]
  exact add_le_add hleft hright

#print axioms rescaledShellProducts_band_mass
#print axioms rescaledShellProducts_interval
#print axioms rescaledShellProducts_prime_mass
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
