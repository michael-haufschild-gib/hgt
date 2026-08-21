import GaloisForLFunctions.RHTower.ConnesLatticeRapidDecay
import GaloisForLFunctions.RHTower.CCMRationalFiniteAdeleDenominator

/-!
# Confinement of the rational denominators and the adelic lattice sum

Appendix I (42)-(46) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

For a test function `f = f_0 ⊗ f_1` the finite factor `f_0` has compact support, so `f(q λ x)`
vanishes unless the finite part of `q` stays in a fixed compact set; the diagonal rationals in a
compact set of finite adeles all lie in one fractional ideal `(1/d)ℤ` (42)/(45) — this is the
corpus's `ccmRationalFiniteAdele_isCompact_rationalDiagonalDenominator`.  Reindexing the sum over
`ℚ^*` by that lattice and applying the Schwartz decay of the archimedean factor gives (46): the
periodization decays faster than every power of the dilation parameter.
-/

open Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

theorem connesLatticeSum_neg (f : SchwartzMap ℝ ℂ) (a : ℝ) :
    connesLatticeSum f (-a) = connesLatticeSum f a := by
  rw [connesLatticeSum, connesLatticeSum]
  have h := (Equiv.neg ℤ).tsum_eq (fun n : ℤ => (if n = 0 then 0 else ‖f (a * (n : ℝ))‖))
  refine Eq.trans ?_ h
  refine tsum_congr fun n => ?_
  by_cases h : n = 0
  · subst h; simp
  · have hneg : (-n : ℤ) ≠ 0 := by simpa using h
    simp only [Equiv.neg_apply, if_neg h, if_neg hneg]
    congr 2
    push_cast
    ring

/-- **Appendix I (46), sign-free form.**  The punctured Schwartz lattice sum decays faster than
every power for any nonzero lattice spacing. -/
theorem connes_latticeSum_rapidDecay' (f : SchwartzMap ℝ ℂ) {c : ℝ} (hc : c ≠ 0) (k : ℕ) :
    Tendsto (fun lam : ℝ => lam ^ k * connesLatticeSum f (lam * c)) atTop (𝓝 0) := by
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · have h := connes_latticeSum_rapidDecay f (c := -c) (by linarith) k
    refine h.congr fun lam => ?_
    congr 1
    rw [show lam * -c = -(lam * c) by ring, connesLatticeSum_neg]
  · exact connes_latticeSum_rapidDecay f hpos k

/-- **Appendix I (42)/(45).**  Diagonal rationals in a compact set of finite adeles lie in one
fractional ideal `(1/d)ℤ`. -/
theorem connes_rationalDiagonal_lattice {K : Set CCMRationalFiniteAdele} (hK : IsCompact K) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ q : ℚ, algebraMap ℚ CCMRationalFiniteAdele q ∈ K →
      ∃ m : ℤ, q = (m : ℚ) / (d : ℚ) := by
  obtain ⟨d, hd, hmem⟩ := ccmRationalFiniteAdele_isCompact_rationalDiagonalDenominator hK
  refine ⟨d, hd, fun q hq => ?_⟩
  obtain ⟨m, hm⟩ := hmem q hq
  refine ⟨m, ?_⟩
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hval : (d : ℚ) * q = (m : ℚ) := by
    have h1 : algebraMap ℤ ℚ d * q = algebraMap ℤ ℚ m := hm.symm
    simpa using h1
  field_simp
  linarith [hval]

/-- **Appendix I (44)-(46).**  A weight supported on the rational diagonal of a compact set of
finite adeles, tested against the archimedean Schwartz factor, decays faster than every power of
the dilation parameter: this is the decay of `E(f)(λx)` for `f = f_0 ⊗ f_1`. -/
theorem connes_adelicShadow_rapidDecay {K : Set CCMRationalFiniteAdele} (hK : IsCompact K)
    (f1 : SchwartzMap ℝ ℂ) {w : ℚ → ℝ} {M : ℝ}
    (hwM : ∀ q : ℚ, |w q| ≤ M)
    (hwsupp : ∀ q : ℚ, w q ≠ 0 → algebraMap ℚ CCMRationalFiniteAdele q ∈ K)
    {xinf : ℝ} (hx : xinf ≠ 0) (k : ℕ) :
    Tendsto (fun lam : ℝ => lam ^ k *
        ∑' q : ℚ, (if q = 0 then 0 else |w q| * ‖f1 ((q : ℝ) * (lam * xinf))‖))
      atTop (𝓝 0) := by
  obtain ⟨d, hd, hlat⟩ := connes_rationalDiagonal_lattice hK
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (w 0)) (hwM 0)
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  set c : ℝ := xinf / (d : ℝ) with hc
  have hcne : c ≠ 0 := div_ne_zero hx hdr
  set i : ℤ → ℚ := fun m => (m : ℚ) / (d : ℚ) with hi
  have hinj : Function.Injective i := by
    intro m n hmn
    simp only [hi] at hmn
    have h : (m : ℚ) = (n : ℚ) := by field_simp at hmn; exact_mod_cast hmn
    exact_mod_cast h
  have hizero : ∀ m : ℤ, i m = 0 ↔ m = 0 := by
    intro m
    constructor
    · intro h
      simp only [hi, div_eq_zero_iff, hdq, or_false] at h
      exact_mod_cast h
    · intro h
      simp [hi, h]
  have hcast : ∀ m : ℤ, ((i m : ℚ) : ℝ) = (m : ℝ) / (d : ℝ) := by
    intro m
    simp only [hi]
    push_cast
    ring
  have hmaj : ∀ lam : ℝ, ∀ m : ℤ,
      (if i m = 0 then 0 else |w (i m)| * ‖f1 (((i m : ℚ) : ℝ) * (lam * xinf))‖)
        ≤ M * (if m = 0 then 0 else ‖f1 (lam * c * (m : ℝ))‖) := by
    intro lam m
    by_cases hm : m = 0
    · have h0 : i m = 0 := (hizero m).mpr hm
      simp only [if_pos h0, if_pos hm, mul_zero, le_refl]
    · have hi0 : i m ≠ 0 := fun h => hm ((hizero m).mp h)
      have harg : ((i m : ℚ) : ℝ) * (lam * xinf) = lam * c * (m : ℝ) := by
        rw [hcast m, hc]
        field_simp
      simp only [if_neg hi0, if_neg hm, harg]
      exact mul_le_mul_of_nonneg_right (hwM _) (norm_nonneg _)
  have hbound : ∀ lam : ℝ, lam ≠ 0 →
      (∑' q : ℚ, (if q = 0 then 0 else |w q| * ‖f1 ((q : ℝ) * (lam * xinf))‖))
        ≤ M * connesLatticeSum f1 (lam * c) := by
    intro lam hlam
    have hac : lam * c ≠ 0 := mul_ne_zero hlam hcne
    have hsummaj : Summable fun m : ℤ =>
        M * (if m = 0 then 0 else ‖f1 (lam * c * (m : ℝ))‖) :=
      (connes_latticeSum_summable f1 hac).mul_left M
    have hsupp : Function.support
        (fun q : ℚ => (if q = 0 then 0 else |w q| * ‖f1 ((q : ℝ) * (lam * xinf))‖))
        ⊆ Set.range i := by
      intro q hq
      simp only [Function.mem_support, ne_eq] at hq
      by_cases hq0 : q = 0
      · exact absurd (by simp [hq0]) hq
      · have hwq : w q ≠ 0 := by
          intro h
          exact hq (by simp [hq0, h])
        obtain ⟨m, hm⟩ := hlat q (hwsupp q hwq)
        exact ⟨m, hm.symm⟩
    rw [← hinj.tsum_eq hsupp]
    have hcomp : Summable fun m : ℤ =>
        (if i m = 0 then 0 else |w (i m)| * ‖f1 (((i m : ℚ) : ℝ) * (lam * xinf))‖) := by
      refine hsummaj.of_nonneg_of_le (fun m => ?_) (fun m => hmaj lam m)
      by_cases hm : i m = 0
      · simp [hm]
      · simp only [if_neg hm]
        positivity
    calc (∑' m : ℤ, (if i m = 0 then 0 else
            |w (i m)| * ‖f1 (((i m : ℚ) : ℝ) * (lam * xinf))‖))
        ≤ ∑' m : ℤ, M * (if m = 0 then 0 else ‖f1 (lam * c * (m : ℝ))‖) :=
          hcomp.tsum_le_tsum (fun m => hmaj lam m) hsummaj
      _ = M * connesLatticeSum f1 (lam * c) := by
          rw [connesLatticeSum, tsum_mul_left]
  have hlim : Tendsto (fun lam : ℝ => M * (lam ^ k * connesLatticeSum f1 (lam * c)))
      atTop (𝓝 0) := by
    simpa using (connes_latticeSum_rapidDecay' f1 hcne k).const_mul M
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with lam hlam
    refine mul_nonneg (by positivity) (tsum_nonneg fun q => ?_)
    by_cases hq : q = 0
    · simp [hq]
    · simp only [if_neg hq]
      positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with lam hlam
    have hlam0 : lam ≠ 0 := by
      intro h
      rw [h] at hlam
      linarith
    have hb := hbound lam hlam0
    calc lam ^ k * ∑' q : ℚ, (if q = 0 then 0 else |w q| * ‖f1 ((q : ℝ) * (lam * xinf))‖)
        ≤ lam ^ k * (M * connesLatticeSum f1 (lam * c)) := by
          refine mul_le_mul_of_nonneg_left hb (by positivity)
      _ = M * (lam ^ k * connesLatticeSum f1 (lam * c)) := by ring

end

end GaloisForLFunctions.RHTower