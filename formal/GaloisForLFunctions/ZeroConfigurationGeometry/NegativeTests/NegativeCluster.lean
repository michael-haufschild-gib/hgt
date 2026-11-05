import GaloisForLFunctions.ZeroConfigurationGeometry.NegativeTests.FourierTail

/-!
# Negative local clusters dominate a small Fourier tail

Critical-line reflection preserves distances and places a point's partner at
twice its depth. A finite height band of nonpositive terms, with one uniformly
negative term, makes the Weil form negative when its absolute Fourier tail is
at most one half.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold

/-- Reflection in the critical line preserves distances. -/
theorem norm_reflect_sub_reflect (p q : ℂ) : ‖reflect p - reflect q‖ = ‖p - q‖ := by
  rw [reflect, reflect,
    show (1 : ℂ) - conj p - (1 - conj q) = conj (q - p) by rw [map_sub]; ring,
    Complex.norm_conj, norm_sub_rev]

/-- The FE partner lies at twice the depth. -/
theorem norm_reflect_sub_eq_twice_depth (p : ℂ) : ‖reflect p - p‖ = 2 * |depth p| := by
  have he : reflect p - p = ((-2 * depth p : ℝ) : ℂ) := by
    apply Complex.ext <;> (simp [reflect, depth]; ring)
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  norm_num


/-- One strictly negative local contribution defeats a small absolute Fourier tail
when every other local contribution is nonpositive. -/
theorem re_W_neg_of_local_nonpositivity {Z : ZeroConfig} {f : ℝ → ℂ} {X R : ℝ} {p : ℂ}
    (hp : p ∈ Z.carrier) (hpR : |p.im - X| ≤ R)
    (hnear : ∀ z ∈ Z.carrier, |z.im - X| ≤ R → (pointImage f f z).re ≤ 0)
    (hpneg : (pointImage f f p).re ≤ -(7 / 16 : ℝ))
    (hs : Summable (fourierFarTerm (multDiff Z emptyZeroConfig) f X R))
    (hL : (∑' z, fourierFarTerm (multDiff Z emptyZeroConfig) f X R z) ≤ 1 / 2) :
    (Z.W f f).re < 0 := by
  classical
  have hfin : {z : ℂ | z ∈ Z.carrier ∧ |z.im - X| ≤ R}.Finite :=
    (Z.window_finite (X - R - 1) (X + R)).subset fun z hz =>
      ⟨hz.1, by linarith only [(abs_le.mp hz.2).1],
        by linarith only [(abs_le.mp hz.2).2]⟩
  set s := hfin.toFinset with hsdef
  have hmem (z : ℂ) : z ∈ s ↔ z ∈ Z.carrier ∧ |z.im - X| ≤ R := by
    simp only [hsdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hpS : p ∈ s := (hmem p).mpr ⟨hp, hpR⟩
  have hsplit (z : ℂ) : multDiff Z emptyZeroConfig z * pointImage f f z =
      (if z ∈ s then multDiff Z emptyZeroConfig z * pointImage f f z else 0) +
      (if R < |z.im - X| then multDiff Z emptyZeroConfig z * pointImage f f z else 0) := by
    by_cases hfar : R < |z.im - X|
    · have hzS : z ∉ s := fun hz => (not_lt_of_ge ((hmem z).mp hz).2) hfar
      rw [if_neg hzS, if_pos hfar, zero_add]
    · rw [if_neg hfar, add_zero]
      by_cases hz : z ∈ Z.carrier
      · rw [if_pos ((hmem z).mpr ⟨hz, not_lt.mp hfar⟩)]
      · have hzS : z ∉ s := fun hh => hz ((hmem z).mp hh).1
        rw [if_neg hzS, multDiff_emptyZeroConfig, Set.indicator_of_notMem hz, zero_mul]
  obtain ⟨hnorm, htail⟩ := quadratic_far_tail_le_square hs
  have hfarS := Summable.of_norm hnorm
  have hdiscS : Summable fun z =>
      if z ∈ s then multDiff Z emptyZeroConfig z * pointImage f f z else 0 :=
    summable_of_ne_finset_zero (s := s) fun z hz => if_neg hz
  have hdisc : (∑' z, (if z ∈ s then multDiff Z emptyZeroConfig z * pointImage f f z else 0)) =
      ∑ z ∈ s, multDiff Z emptyZeroConfig z * pointImage f f z := by
    rw [tsum_eq_sum (s := s) fun z hz => if_neg hz]
    exact Finset.sum_congr rfl fun z hz => if_pos hz
  have hW : Z.W f f = (∑ z ∈ s, multDiff Z emptyZeroConfig z * pointImage f f z) +
      ∑' z, (if R < |z.im - X| then multDiff Z emptyZeroConfig z * pointImage f f z else 0) := by
    rw [W_eq_tsum_indicator]
    simp only [← multDiff_emptyZeroConfig]
    rw [tsum_congr hsplit, hdiscS.tsum_add hfarS, hdisc]
  have hterm (z : ℂ) (hz : z ∈ s) :
      (multDiff Z emptyZeroConfig z * pointImage f f z).re =
        (Z.mult z : ℝ) * (pointImage f f z).re := by
    rw [multDiff_emptyZeroConfig, Set.indicator_of_mem ((hmem z).mp hz).1]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  have hnonpos (z : ℂ) (hz : z ∈ s) :
      (multDiff Z emptyZeroConfig z * pointImage f f z).re ≤ 0 := by
    rw [hterm z hz]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
      (hnear z ((hmem z).mp hz).1 ((hmem z).mp hz).2)
  have hpterm : (multDiff Z emptyZeroConfig p * pointImage f f p).re ≤ -(7 / 16 : ℝ) := by
    rw [hterm p hpS]
    have hm : (1 : ℝ) ≤ Z.mult p := by exact_mod_cast Z.one_le_mult p hp
    have hh := mul_le_mul_of_nonneg_left hpneg (Nat.cast_nonneg (Z.mult p) : (0 : ℝ) ≤ Z.mult p)
    linarith only [hh, hm]
  have hsum : (∑ z ∈ s, multDiff Z emptyZeroConfig z * pointImage f f z).re ≤ -(7 / 16 : ℝ) := by
    rw [Complex.re_sum, ← Finset.add_sum_erase _ _ hpS]
    have hrest : (∑ z ∈ s.erase p, (multDiff Z emptyZeroConfig z * pointImage f f z).re) ≤ 0 :=
      Finset.sum_nonpos fun z hz => hnonpos z (Finset.mem_of_mem_erase hz)
    linarith only [hpterm, hrest]
  have hL0 : 0 ≤ ∑' z, fourierFarTerm (multDiff Z emptyZeroConfig) f X R z :=
    tsum_nonneg (fourierFarTerm_nonneg (multDiff Z emptyZeroConfig) f X R)
  have hLsq := pow_le_pow_left₀ hL0 hL 2
  have hfarRe := (Complex.re_le_norm (∑' z, (if R < |z.im - X| then
    multDiff Z emptyZeroConfig z * pointImage f f z else 0))).trans htail
  rw [hW, Complex.add_re]
  linarith only [hsum, hfarRe, hLsq]


end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.norm_reflect_sub_reflect
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.norm_reflect_sub_eq_twice_depth
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.re_W_neg_of_local_nonpositivity
