import GaloisForLFunctions.RHTower.WeilLogShiftGramImageDensity
import GaloisForLFunctions.RHTower.WeilLogShiftGramCardinalityLower

/-!
# Exact minimal cardinality of normalized finite Gram certificates

Approximate an enlarged coordinate simplex by actual single-test vectors.
The coordinate error leaves a uniform strict norm margin. Together with the
dimension obstruction this gives exactly one more test than coefficients.
-/

open scoped BigOperators

namespace RHTower

theorem exists_finiteWeilGram_card_le_succ_certificate (s : Finset ℕ) :
    ∃ tests : Finset FiniteWeilGramTest, tests.card ≤ s.card + 1 ∧
      FiniteWeilGramNormCertificate s tests := by
  classical
  let d : ℝ := s.card
  let A : ℝ := 2 * (d + 1) ^ 2
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hA : 0 < A := by dsimp [A]; positivity
  let target : Option s → s → ℝ
    | none => fun _ => -A
    | some i => A • Pi.single i 1
  have happ (o : Option s) : ∃ w : FiniteWeilGramTest,
      dist (target o) (finiteWeilGramCoefficientVector s w) < 1 :=
    (denseRange_finiteWeilGramCoefficientVector s).exists_dist_lt (target o) zero_lt_one
  choose w hw using happ
  have hdist (o : Option s) : ‖finiteWeilGramCoefficientVector s (w o) - target o‖ ≤ 1 := by
    have h := (hw o).le
    rwa [dist_comm, dist_eq_norm] at h
  have herror (o : Option s) (c : s → ℝ) :
      |finiteWeilGramForm s (w o) c - ∑ i, target o i * c i| ≤ d * ‖c‖ := by
    have heq : finiteWeilGramForm s (w o) c - ∑ i, target o i * c i =
        ∑ i, (finiteWeilGramCoefficientVector s (w o) i - target o i) * c i := by
      rw [finiteWeilGramCoefficientVector_pairing]
      simp only [sub_mul, Finset.sum_sub_distrib]
    rw [heq]
    calc
      |∑ i, (finiteWeilGramCoefficientVector s (w o) i - target o i) * c i| ≤
          ∑ i, |finiteWeilGramCoefficientVector s (w o) i - target o i| * |c i| := by
        simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (s := Finset.univ)
          (f := fun i => (finiteWeilGramCoefficientVector s (w o) i - target o i) * c i)
      _ ≤ ∑ _i : s, ‖c‖ := by
        apply Finset.sum_le_sum
        intro i hi
        have hv : |finiteWeilGramCoefficientVector s (w o) i - target o i| ≤ 1 := by
          simpa only [Pi.sub_apply, Real.norm_eq_abs] using
            (norm_le_pi_norm (finiteWeilGramCoefficientVector s (w o) - target o) i).trans (hdist o)
        have hc : |c i| ≤ ‖c‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm c i
        simpa only [one_mul] using mul_le_mul hv hc (abs_nonneg _) zero_le_one
      _ = d * ‖c‖ := by simp [d]
  let tests : Finset FiniteWeilGramTest := Finset.univ.image w
  have hcard : tests.card ≤ s.card + 1 := by
    calc
      tests.card ≤ (Finset.univ : Finset (Option s)).card := Finset.card_image_le
      _ = s.card + 1 := by simp
  refine ⟨tests, hcard, ?_⟩
  intro c hc0
  by_contra hbad
  push Not at hbad
  have htest (o : Option s) : -‖c‖ ≤ finiteWeilGramForm s (w o) c :=
    hbad (w o) (Finset.mem_image.mpr ⟨o, Finset.mem_univ o, rfl⟩)
  have htarget (o : Option s) : -(d + 1) * ‖c‖ ≤ ∑ i, target o i * c i := by
    have he := (abs_le.mp (herror o c)).2
    linarith [htest o]
  have hlow (i : s) : -(d + 1) * ‖c‖ ≤ A * c i := by
    simpa [target, Pi.single_apply] using htarget (some i)
  have hsum : A * (∑ i, c i) ≤ (d + 1) * ‖c‖ := by
    have ht := htarget none
    simp only [target, ← Finset.mul_sum] at ht
    nlinarith
  have hupp (i : s) : A * c i ≤ d * (d + 1) * ‖c‖ := by
    have hcountNat : (Finset.univ.erase i).card + 1 = s.card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_coe]
      have hp := Finset.card_pos.mpr (show s.Nonempty from ⟨i.1, i.2⟩)
      omega
    have hcountReal : ((Finset.univ.erase i).card : ℝ) + 1 = d := by
      dsimp [d]
      exact_mod_cast hcountNat
    have hcount : ((Finset.univ.erase i).card : ℝ) = d - 1 := by linarith
    have hrest : ((Finset.univ.erase i).card : ℝ) * (-(d + 1) * ‖c‖) ≤
        ∑ j ∈ Finset.univ.erase i, A * c j := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        (Finset.sum_le_sum (s := Finset.univ.erase i) (fun j _ => hlow j))
    rw [hcount] at hrest
    have heq := Finset.sum_erase_add Finset.univ (fun j : s => A * c j) (Finset.mem_univ i)
    simp only [← Finset.mul_sum] at hrest heq
    nlinarith
  have habs (i : s) : |A * c i| ≤ (d + 1) ^ 2 * ‖c‖ := by
    have hn : 0 ≤ ‖c‖ := norm_nonneg c
    have hprod : 0 ≤ d * ((d + 1) * ‖c‖) := mul_nonneg hd (by positivity)
    apply abs_le.mpr
    constructor
    · nlinarith [hlow i]
    · nlinarith [hupp i]
  have hnorm : ‖A • c‖ ≤ (d + 1) ^ 2 * ‖c‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs] using habs i
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hA] at hnorm
  have hpos : 0 < (d + 1) ^ 2 * ‖c‖ := by
    exact mul_pos (by positivity) (norm_pos_iff.mpr hc0)
  dsimp [A] at hnorm
  nlinarith

/-- The minimum number is zero on the empty support and exactly `d+1` on a
nonempty support of cardinality `d`. -/
theorem exists_finiteWeilGram_minimal_card_certificate (s : Finset ℕ) :
    ∃ tests : Finset FiniteWeilGramTest, FiniteWeilGramNormCertificate s tests ∧
      tests.card = (if s = ∅ then 0 else s.card + 1) ∧
      ∀ other : Finset FiniteWeilGramTest, FiniteWeilGramNormCertificate s other →
        tests.card ≤ other.card := by
  classical
  by_cases hs : s = ∅
  · subst s
    refine ⟨∅, ?_, by simp, ?_⟩
    · intro c hc
      apply False.elim
      apply hc
      funext i
      exact False.elim (Finset.notMem_empty i.1 i.2)
    · intro other _
      simp
  · have hnonempty : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
    obtain ⟨tests, hcard, hcert⟩ := exists_finiteWeilGram_card_le_succ_certificate s
    have heq : tests.card = s.card + 1 :=
      le_antisymm hcard (finiteWeilGram_certificate_card_lower hnonempty hcert)
    refine ⟨tests, hcert, by simp only [hs, if_false, heq], ?_⟩
    intro other hother
    rw [heq]
    exact finiteWeilGram_certificate_card_lower hnonempty hother

end RHTower
