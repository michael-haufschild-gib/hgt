import GaloisForLFunctions.RHTower.GammaCutoffCommutatorBridge

/-!
# Compactly supported data have a two-sided Gamma wall

Two facts, both elementary, that put every `χ′`-term of `(14)` in the block source class.

A bounded profile supported in `[−R,R]` obeys `|g(L)| ≤ Be^{R}e^{-|L|}` trivially.  Its *transport*
obeys the same kind of bound for a different reason: past the support the diagonal term vanishes and
the two translates can only reach the support at scale `s ≥ |L| − R`, where the kernel has already
decayed exponentially.  So the transport of a compactly supported profile is `O(e^{-|L|})` as well,
and `gammaWallBlockNorm_lt_top_of_exp_wall` applies to both.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- A bounded compactly supported profile has a two-sided exponential wall. -/
theorem norm_le_exp_of_compactSupport {g : ℝ → ℝ} {B R : ℝ} (hB : ∀ x, |g x| ≤ B)
    (hsupp : ∀ x : ℝ, R < |x| → g x = 0) (L : ℝ) :
    |g L| ≤ (B * Real.exp R) * Real.exp (-|L|) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  rcases le_or_gt |L| R with h | h
  · have hexp : Real.exp R * Real.exp (-|L|) = Real.exp (R - |L|) := by
      rw [← Real.exp_add]
      ring_nf
    have h1 : (1 : ℝ) ≤ Real.exp (R - |L|) := Real.one_le_exp (by linarith)
    calc |g L| ≤ B := hB L
      _ = B * 1 := (mul_one B).symm
      _ ≤ B * Real.exp (R - |L|) := mul_le_mul_of_nonneg_left h1 hB0
      _ = (B * Real.exp R) * Real.exp (-|L|) := by rw [← hexp]; ring
  · rw [hsupp L h, abs_zero]
    positivity

/-- **The transport of a compactly supported profile has a two-sided exponential wall.** -/
theorem abs_gammaTransport_le_exp_of_compactSupport {g g' : ℝ → ℝ} {B M R : ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hM : ∀ x, |g' x| ≤ M)
    (hB : ∀ x, |g x| ≤ B) (hsupp : ∀ x : ℝ, R < |x| → g x = 0)
    {L : ℝ} (hL : R + 2 ≤ |L|) :
    |gammaTransport g L| ≤ (8 * B * Real.exp (R + 1)) * Real.exp (-|L|) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  set a : ℝ := |L| - R - 1 with hadef
  have ha1 : (1 : ℝ) ≤ a := by rw [hadef]; linarith
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha1
  have hint := integrableOn_secondDifference_mul_kernel hg hM L
  have hvanish : ∀ s ∈ Ioc (0 : ℝ) a, secondDifference g L s * gammaTransportKernel s = 0 := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs.1
    have hsa : s ≤ a := hs.2
    have habs : |s| = s := abs_of_pos hs0
    have h0 : g L = 0 := hsupp L (by rw [hadef] at hsa; linarith)
    have hplus : |L| ≤ |L + s| + |s| := by
      have h := abs_sub (L + s) s
      simpa using h
    have hminus : |L| ≤ |L - s| + |s| := by
      have h := abs_add_le (L - s) s
      simpa using h
    have h1 : g (L + s) = 0 := by
      refine hsupp _ ?_
      rw [habs] at hplus
      rw [hadef] at hsa
      linarith
    have h2 : g (L - s) = 0 := by
      refine hsupp _ ?_
      rw [habs] at hminus
      rw [hadef] at hsa
      linarith
    rw [secondDifference, h0, h1, h2]
    ring
  have hsplit : Ioi (0 : ℝ) = Ioc 0 a ∪ Ioi a := (Ioc_union_Ioi_eq_Ioi ha0.le).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) a) (Ioi a) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact absurd ht.2 (not_le.mpr ht')
  have h1 : IntegrableOn (fun s => secondDifference g L s * gammaTransportKernel s) (Ioc 0 a) :=
    hint.mono_set (by rw [hsplit]; exact subset_union_left)
  have h2 : IntegrableOn (fun s => secondDifference g L s * gammaTransportKernel s) (Ioi a) :=
    hint.mono_set (by rw [hsplit]; exact subset_union_right)
  have hzero : (∫ s in Ioc (0 : ℝ) a, secondDifference g L s * gammaTransportKernel s) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun s hs => hvanish s hs
  have hrepr : gammaTransport g L
      = ∫ s in Ioi a, secondDifference g L s * gammaTransportKernel s := by
    rw [gammaTransport, hsplit, setIntegral_union hdisj measurableSet_Ioi h1 h2, hzero, zero_add]
  have hbd : ∀ s ∈ Ioi a, ‖secondDifference g L s * gammaTransportKernel s‖
      ≤ 8 * B * Real.exp (-s) := by
    intro s hs
    have hsa : a < s := hs
    have hs1 : (1 : ℝ) ≤ s := le_trans ha1 hsa.le
    have hkpos : 0 < gammaTransportKernel s := gammaTransportKernel_pos (by linarith)
    have hk : gammaTransportKernel s ≤ 2 * Real.exp (-s) :=
      gammaTransportKernel_le_two_mul_exp_neg hs1
    have hsd : |secondDifference g L s| ≤ 4 * B :=
      abs_secondDifference_le_of_bounded hB L s
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hkpos]
    calc |secondDifference g L s| * gammaTransportKernel s
        ≤ (4 * B) * (2 * Real.exp (-s)) :=
          mul_le_mul hsd hk hkpos.le (by positivity)
      _ = 8 * B * Real.exp (-s) := by ring
  have hmaj : IntegrableOn (fun s : ℝ => 8 * B * Real.exp (-s)) (Ioi a) := by
    have h : IntegrableOn (fun x : ℝ => Real.exp (-1 * x)) (Ioi a) :=
      exp_neg_integrableOn_Ioi a one_pos
    have h' : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi a) := by
      refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
      norm_num
    exact h'.const_mul _
  have hle := MeasureTheory.norm_integral_le_of_norm_le hmaj
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs using hbd s hs)
  rw [integral_const_mul, integral_exp_neg_Ioi] at hle
  rw [hrepr, ← Real.norm_eq_abs]
  refine le_trans hle (le_of_eq ?_)
  rw [hadef, show (8 : ℝ) * B * Real.exp (R + 1) * Real.exp (-|L|)
      = 8 * B * (Real.exp (R + 1) * Real.exp (-|L|)) by ring, ← Real.exp_add]
  congr 2
  ring

end GaloisForLFunctions.RHTower
