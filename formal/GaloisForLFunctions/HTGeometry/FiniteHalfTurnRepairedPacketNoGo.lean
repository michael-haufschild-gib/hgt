import GaloisForLFunctions.HTGeometry.StieltjesSemidefiniteCriterion
import GaloisForLFunctions.HTGeometry.SingleEvenFrequency
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Finite half-turn repaired packets are not Stieltjes moment sequences

For a finite packet with positive, distinct nodes, the largest node dominates
with exponentially small relative error.  This yields the rate
`k * (M k * M (k + 2) / M (k + 1) ^ 2 - 1) → 0`, which is strong enough to
overcome the factorial correction approaching one from below.  Consequently,
an adjacent Hankel determinant of the repaired sequence is eventually negative.
-/

open scoped BigOperators
open Filter MeasureTheory Polynomial
open HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def normalizedFinitePacketMoment (c x : ι → ℝ) (i₀ : ι) (k : ℕ) : ℝ :=
  ∑ i, c i * (x i / x i₀) ^ k

theorem normalizedFinitePacketMoment_sub_dominant
    (c x : ι → ℝ) (i₀ : ι) (k : ℕ) (hx0 : x i₀ ≠ 0) :
    normalizedFinitePacketMoment c x i₀ k - c i₀ =
      ∑ i ∈ Finset.univ.erase i₀, c i * (x i / x i₀) ^ k := by
  rw [normalizedFinitePacketMoment]
  have hi : i₀ ∈ (Finset.univ : Finset ι) := Finset.mem_univ i₀
  rw [← Finset.sum_erase_add _ _ hi]
  simp [hx0]

theorem tendsto_normalizedFinitePacketMoment_error_mul_natCast
    (c x : ι → ℝ) (i₀ : ι) (d : ℕ)
    (hx : ∀ i, 0 < x i) (hmax : ∀ i, i ≠ i₀ → x i < x i₀) :
    Tendsto
      (fun k : ℕ => (k : ℝ) *
        (normalizedFinitePacketMoment c x i₀ (k + d) - c i₀))
      atTop (nhds 0) := by
  have hx0 : x i₀ ≠ 0 := (hx i₀).ne'
  rw [show (fun k : ℕ => (k : ℝ) *
      (normalizedFinitePacketMoment c x i₀ (k + d) - c i₀)) =
      fun k : ℕ => ∑ i ∈ Finset.univ.erase i₀,
        (c i * (x i / x i₀) ^ d) * ((k : ℝ) * (x i / x i₀) ^ k) by
    funext k
    rw [normalizedFinitePacketMoment_sub_dominant c x i₀ (k + d) hx0]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_add]
    ring]
  have hsum : Tendsto
      (fun k : ℕ => ∑ i ∈ Finset.univ.erase i₀,
        (c i * (x i / x i₀) ^ d) * ((k : ℝ) * (x i / x i₀) ^ k))
      atTop (nhds (∑ _i ∈ Finset.univ.erase i₀, (0 : ℝ))) := by
    apply tendsto_finsetSum (Finset.univ.erase i₀)
    intro i hi
    have hine : i ≠ i₀ := Finset.ne_of_mem_erase hi
    have hr0 : 0 ≤ x i / x i₀ := div_nonneg (hx i).le (hx i₀).le
    have hr1 : x i / x i₀ < 1 := (div_lt_one (hx i₀)).2 (hmax i hine)
    have hpow := tendsto_pow_const_mul_const_pow_of_lt_one 1 hr0 hr1
    simpa [pow_one, mul_assoc, mul_left_comm, mul_comm] using
      hpow.const_mul (c i * (x i / x i₀) ^ d)
  simpa using hsum

theorem tendsto_normalizedFinitePacketMoment_shift
    (c x : ι → ℝ) (i₀ : ι) (d : ℕ)
    (hx : ∀ i, 0 < x i) (hmax : ∀ i, i ≠ i₀ → x i < x i₀) :
    Tendsto (fun k : ℕ => normalizedFinitePacketMoment c x i₀ (k + d))
      atTop (nhds (c i₀)) := by
  have hx0 : x i₀ ≠ 0 := (hx i₀).ne'
  rw [show (fun k : ℕ => normalizedFinitePacketMoment c x i₀ (k + d)) =
      fun k : ℕ => c i₀ + ∑ i ∈ Finset.univ.erase i₀,
        (c i * (x i / x i₀) ^ d) * (x i / x i₀) ^ k by
    funext k
    calc
      normalizedFinitePacketMoment c x i₀ (k + d) =
          c i₀ + (normalizedFinitePacketMoment c x i₀ (k + d) - c i₀) := by ring
      _ = c i₀ + ∑ i ∈ Finset.univ.erase i₀,
          c i * (x i / x i₀) ^ (k + d) := by
        rw [normalizedFinitePacketMoment_sub_dominant c x i₀ (k + d) hx0]
      _ = c i₀ + ∑ i ∈ Finset.univ.erase i₀,
          (c i * (x i / x i₀) ^ d) * (x i / x i₀) ^ k := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [pow_add]
        ring]
  have hsum : Tendsto
      (fun k : ℕ => ∑ i ∈ Finset.univ.erase i₀,
        (c i * (x i / x i₀) ^ d) * (x i / x i₀) ^ k)
      atTop (nhds 0) := by
    have hsum' : Tendsto
        (fun k : ℕ => ∑ i ∈ Finset.univ.erase i₀,
          (c i * (x i / x i₀) ^ d) * (x i / x i₀) ^ k)
        atTop (nhds (∑ _i ∈ Finset.univ.erase i₀, (0 : ℝ))) := by
      apply tendsto_finsetSum (Finset.univ.erase i₀)
      intro i hi
      have hine : i ≠ i₀ := Finset.ne_of_mem_erase hi
      have hr0 : 0 ≤ x i / x i₀ := div_nonneg (hx i).le (hx i₀).le
      have hr1 : x i / x i₀ < 1 := (div_lt_one (hx i₀)).2 (hmax i hine)
      have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
      simpa [mul_assoc] using hpow.const_mul (c i * (x i / x i₀) ^ d)
    simpa using hsum'
  simpa using tendsto_const_nhds.add hsum

omit [DecidableEq ι] in
theorem normalizedFinitePacketMoment_pos
    (c x : ι → ℝ) (i₀ : ι) (k : ℕ)
    (hc : ∀ i, 0 < c i) (hx : ∀ i, 0 < x i) :
    0 < normalizedFinitePacketMoment c x i₀ k := by
  letI : Nonempty ι := ⟨i₀⟩
  apply Finset.sum_pos
  · intro i hi
    exact mul_pos (hc i) (pow_pos (div_pos (hx i) (hx i₀)) k)
  · exact Finset.univ_nonempty

theorem tendsto_normalizedFinitePacketMoment_ratio_error_mul_natCast
    (c x : ι → ℝ) (i₀ : ι)
    (hc : ∀ i, 0 < c i) (hx : ∀ i, 0 < x i)
    (hmax : ∀ i, i ≠ i₀ → x i < x i₀) :
    Tendsto
      (fun k : ℕ => (k : ℝ) *
        (normalizedFinitePacketMoment c x i₀ k *
              normalizedFinitePacketMoment c x i₀ (k + 2) /
            normalizedFinitePacketMoment c x i₀ (k + 1) ^ 2 - 1))
      atTop (nhds 0) := by
  let A := normalizedFinitePacketMoment c x i₀
  let C := c i₀
  have hA0 : Tendsto (fun k : ℕ => A k) atTop (nhds C) := by
    simpa [A, C] using tendsto_normalizedFinitePacketMoment_shift c x i₀ 0 hx hmax
  have hA1 : Tendsto (fun k : ℕ => A (k + 1)) atTop (nhds C) := by
    simpa [A, C] using tendsto_normalizedFinitePacketMoment_shift c x i₀ 1 hx hmax
  have hA2 : Tendsto (fun k : ℕ => A (k + 2)) atTop (nhds C) := by
    simpa [A, C] using tendsto_normalizedFinitePacketMoment_shift c x i₀ 2 hx hmax
  have he0 : Tendsto (fun k : ℕ => (k : ℝ) * (A k - C)) atTop (nhds 0) := by
    simpa [A, C] using
      tendsto_normalizedFinitePacketMoment_error_mul_natCast c x i₀ 0 hx hmax
  have he1 : Tendsto (fun k : ℕ => (k : ℝ) * (A (k + 1) - C)) atTop (nhds 0) := by
    simpa [A, C] using
      tendsto_normalizedFinitePacketMoment_error_mul_natCast c x i₀ 1 hx hmax
  have he2 : Tendsto (fun k : ℕ => (k : ℝ) * (A (k + 2) - C)) atTop (nhds 0) := by
    simpa [A, C] using
      tendsto_normalizedFinitePacketMoment_error_mul_natCast c x i₀ 2 hx hmax
  have hnum : Tendsto
      (fun k : ℕ => (k : ℝ) * (A k * A (k + 2) - A (k + 1) ^ 2))
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _k : ℕ => C) atTop (nhds C) := tendsto_const_nhds
    have hterm0 : Tendsto
        (fun k : ℕ => ((k : ℝ) * (A k - C)) * A (k + 2))
        atTop (nhds 0) := by simpa using he0.mul hA2
    have hterm2 : Tendsto
        (fun k : ℕ => C * ((k : ℝ) * (A (k + 2) - C)))
        atTop (nhds 0) := by simpa using he2.const_mul C
    have hterm1 : Tendsto
        (fun k : ℕ => ((k : ℝ) * (A (k + 1) - C)) * (A (k + 1) + C))
        atTop (nhds 0) := by
      simpa using he1.mul (hA1.add hconst)
    have h := (hterm0.add hterm2).sub hterm1
    convert h using 1
    · funext k
      ring
    · norm_num
  have hden : Tendsto (fun k : ℕ => A (k + 1) ^ 2) atTop (nhds (C ^ 2)) := hA1.pow 2
  have hCne : C ^ 2 ≠ 0 := pow_ne_zero 2 (hc i₀).ne'
  have hquot := hnum.div hden hCne
  have hfun :
      (fun k : ℕ => (k : ℝ) * (A k * A (k + 2) / A (k + 1) ^ 2 - 1)) =
      fun k : ℕ => ((k : ℝ) * (A k * A (k + 2) - A (k + 1) ^ 2)) /
        A (k + 1) ^ 2 := by
    funext k
    have hApos : 0 < A (k + 1) :=
      normalizedFinitePacketMoment_pos c x i₀ (k + 1) hc hx
    field_simp [hApos.ne']
  rw [hfun]
  change Tendsto
    ((fun k : ℕ => (k : ℝ) * (A k * A (k + 2) - A (k + 1) ^ 2)) /
      fun k : ℕ => A (k + 1) ^ 2) atTop (nhds 0)
  simpa only [zero_div] using hquot

theorem eventually_normalizedFinitePacketMoment_factorial_ratio_lt_one
    (c x : ι → ℝ) (i₀ : ι)
    (hc : ∀ i, 0 < c i) (hx : ∀ i, 0 < x i)
    (hmax : ∀ i, i ≠ i₀ → x i < x i₀) :
    ∀ᶠ k : ℕ in atTop,
      (normalizedFinitePacketMoment c x i₀ k *
              normalizedFinitePacketMoment c x i₀ (k + 2) /
            normalizedFinitePacketMoment c x i₀ (k + 1) ^ 2) *
          (((2 * k : ℕ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ) /
            (((2 * k + 2 : ℕ) : ℝ) * ((2 * k + 3 : ℕ) : ℝ))) < 1 := by
  let ratio : ℕ → ℝ := fun k =>
    normalizedFinitePacketMoment c x i₀ k *
          normalizedFinitePacketMoment c x i₀ (k + 2) /
        normalizedFinitePacketMoment c x i₀ (k + 1) ^ 2
  have hrate : Tendsto (fun k : ℕ => (k : ℝ) * (ratio k - 1)) atTop (nhds 0) := by
    simpa [ratio] using
      tendsto_normalizedFinitePacketMoment_ratio_error_mul_natCast c x i₀ hc hx hmax
  have hsmall : ∀ᶠ k : ℕ in atTop, (k : ℝ) * (ratio k - 1) < 1 :=
    hrate.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hkpos : ∀ᶠ k : ℕ in atTop, 1 ≤ k := eventually_atTop.2 ⟨1, fun _ hk => hk⟩
  filter_upwards [hsmall, hkpos] with k hsmallk hk
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hratio : ratio k < 1 + 1 / (k : ℝ) := by
    have hdiff : ratio k - 1 < 1 / (k : ℝ) := by
      apply (lt_div_iff₀ hkR).2
      simpa [mul_comm] using hsmallk
    linarith
  have hfacpos : 0 <
      (((2 * k : ℕ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ) /
        (((2 * k + 2 : ℕ) : ℝ) * ((2 * k + 3 : ℕ) : ℝ))) := by positivity
  calc
    ratio k *
          (((2 * k : ℕ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ) /
            (((2 * k + 2 : ℕ) : ℝ) * ((2 * k + 3 : ℕ) : ℝ))) <
        (1 + 1 / (k : ℝ)) *
          (((2 * k : ℕ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ) /
            (((2 * k + 2 : ℕ) : ℝ) * ((2 * k + 3 : ℕ) : ℝ))) :=
      mul_lt_mul_of_pos_right hratio hfacpos
    _ < 1 := by
      push_cast
      field_simp
      nlinarith

theorem eventually_normalizedFinitePacketMoment_weighted_gap
    (c x : ι → ℝ) (i₀ : ι)
    (hc : ∀ i, 0 < c i) (hx : ∀ i, 0 < x i)
    (hmax : ∀ i, i ≠ i₀ → x i < x i₀) :
    ∀ᶠ k : ℕ in atTop,
      (((2 * k : ℕ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ)) *
          (normalizedFinitePacketMoment c x i₀ k *
            normalizedFinitePacketMoment c x i₀ (k + 2)) <
        (((2 * k + 2 : ℕ) : ℝ) * ((2 * k + 3 : ℕ) : ℝ)) *
          normalizedFinitePacketMoment c x i₀ (k + 1) ^ 2 := by
  have hratio := eventually_normalizedFinitePacketMoment_factorial_ratio_lt_one
    c x i₀ hc hx hmax
  have hkpos : ∀ᶠ k : ℕ in atTop, 1 ≤ k := eventually_atTop.2 ⟨1, fun _ hk => hk⟩
  filter_upwards [hratio, hkpos] with k hratio hk
  have hApos : 0 < normalizedFinitePacketMoment c x i₀ (k + 1) :=
    normalizedFinitePacketMoment_pos c x i₀ (k + 1) hc hx
  have hdenpos : 0 <
      (((2 * k + 2 : ℕ) : ℝ) * ((2 * k + 3 : ℕ) : ℝ)) := by positivity
  have hleftpos : 0 <
      (((2 * k : ℕ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ)) := by positivity
  field_simp [hApos.ne', hdenpos.ne'] at hratio
  nlinarith

theorem shiftedMomentFunctional_cauchy_schwarz
    {s : ℕ → ℝ}
    (hshift : ∀ r : Polynomial ℝ, 0 ≤ momentFunctional s (Polynomial.X * r ^ 2))
    (p q : Polynomial ℝ) :
    momentFunctional s (Polynomial.X * (p * q)) ^ 2 ≤
      momentFunctional s (Polynomial.X * p ^ 2) *
        momentFunctional s (Polynomial.X * q ^ 2) := by
  have hquad : ∀ t : ℝ,
      0 ≤ momentFunctional s (Polynomial.X * q ^ 2) * (t * t) +
        (2 * momentFunctional s (Polynomial.X * (p * q))) * t +
        momentFunctional s (Polynomial.X * p ^ 2) := by
    intro t
    have hpoly : Polynomial.X * (p + t • q) ^ 2 =
        Polynomial.X * p ^ 2 +
          (2 * t) • (Polynomial.X * (p * q)) +
          (t ^ 2) • (Polynomial.X * q ^ 2) := by
      simp only [Polynomial.smul_eq_C_mul, map_mul, map_pow, map_ofNat]
      ring
    have heq : momentFunctional s (Polynomial.X * (p + t • q) ^ 2) =
        momentFunctional s (Polynomial.X * q ^ 2) * (t * t) +
          (2 * momentFunctional s (Polynomial.X * (p * q))) * t +
          momentFunctional s (Polynomial.X * p ^ 2) := by
      rw [hpoly, momentFunctional_add, momentFunctional_add,
        momentFunctional_smul, momentFunctional_smul]
      ring
    rw [← heq]
    exact hshift _
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  nlinarith [hd]

theorem adjacentHankel_nonneg_of_hasStieltjesMoments
    {s : ℕ → ℝ} {μ : MeasureTheory.Measure ℝ}
    (hrep : HasStieltjesMoments s μ) (k : ℕ) :
    0 ≤ s k * s (k + 2) - s (k + 1) ^ 2 := by
  rcases hrep with ⟨hmom, hsupport⟩
  have hs : ∀ n, s n = ∫ x : ℝ, x ^ n ∂μ := fun n => (hmom n).2.symm
  have hint : ∀ n, MeasureTheory.Integrable (fun x : ℝ => x ^ n) μ :=
    fun n => (hmom n).1
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · have hcs := momentFunctional_cauchy_schwarz s hs hint
      (Polynomial.X ^ m) (Polynomial.X ^ (m + 1))
    have hpq : momentFunctional s
        ((Polynomial.X ^ m) * (Polynomial.X ^ (m + 1))) = s (2 * m + 1) := by
      rw [← pow_add, momentFunctional_X_pow]
      congr 1
      omega
    have hpp : momentFunctional s ((Polynomial.X ^ m) ^ 2) = s (2 * m) := by
      rw [← pow_mul, momentFunctional_X_pow]
      congr 1
      omega
    have hqq : momentFunctional s ((Polynomial.X ^ (m + 1)) ^ 2) = s (2 * m + 2) := by
      rw [← pow_mul, momentFunctional_X_pow]
      congr 1
      omega
    rw [hpq, hpp, hqq] at hcs
    convert sub_nonneg.mpr hcs using 1
  · have hshift : ∀ r : Polynomial ℝ,
        0 ≤ momentFunctional s (Polynomial.X * r ^ 2) :=
      momentFunctional_X_mul_sq_nonneg s hs hint hsupport
    have hcs := shiftedMomentFunctional_cauchy_schwarz hshift
      (Polynomial.X ^ m) (Polynomial.X ^ (m + 1))
    have hpq : momentFunctional s
        (Polynomial.X * ((Polynomial.X ^ m) * (Polynomial.X ^ (m + 1)))) =
          s (2 * m + 2) := by
      rw [← pow_add, ← pow_succ', momentFunctional_X_pow]
      congr 1
      omega
    have hpp : momentFunctional s
        (Polynomial.X * (Polynomial.X ^ m) ^ 2) = s (2 * m + 1) := by
      rw [← pow_mul, ← pow_succ', momentFunctional_X_pow]
      congr 1
      omega
    have hqq : momentFunctional s
        (Polynomial.X * (Polynomial.X ^ (m + 1)) ^ 2) = s (2 * m + 3) := by
      rw [← pow_mul, ← pow_succ', momentFunctional_X_pow]
      congr 1
      omega
    rw [hpq, hpp, hqq] at hcs
    convert sub_nonneg.mpr hcs using 1

def finitePositivePacketMoment (nodes : Finset ℝ) (c : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∑ x : {x // x ∈ nodes}, c x * (x : ℝ) ^ k

def halfTurnRepairedPacketMoment (nodes : Finset ℝ) (c : ℝ → ℝ) (k : ℕ) : ℝ :=
  finitePositivePacketMoment nodes c k / (Nat.factorial (2 * k - 1) : ℝ)

noncomputable def finitePositivePacketTop (nodes : Finset ℝ) (hne : nodes.Nonempty) :
    {x // x ∈ nodes} :=
  ⟨nodes.max' hne, nodes.max'_mem hne⟩

theorem finitePositivePacketTop_pos
    (nodes : Finset ℝ) (hne : nodes.Nonempty)
    (hx : ∀ x ∈ nodes, 0 < x) :
    0 < (finitePositivePacketTop nodes hne : ℝ) :=
  hx _ (finitePositivePacketTop nodes hne).property

theorem finitePositivePacket_lt_top_of_ne
    (nodes : Finset ℝ) (hne : nodes.Nonempty)
    {x : {x // x ∈ nodes}} (hneTop : x ≠ finitePositivePacketTop nodes hne) :
    (x : ℝ) < finitePositivePacketTop nodes hne := by
  have hle : (x : ℝ) ≤ nodes.max' hne := Finset.le_max' nodes x x.property
  have hneval : (x : ℝ) ≠ nodes.max' hne := by
    intro h
    apply hneTop
    apply Subtype.ext
    exact h
  exact lt_of_le_of_ne hle hneval

theorem finitePositivePacketMoment_eq_top_pow_mul_normalized
    (nodes : Finset ℝ) (hne : nodes.Nonempty) (c : ℝ → ℝ) (k : ℕ)
    (hx : ∀ x ∈ nodes, 0 < x) :
    finitePositivePacketMoment nodes c k =
      (finitePositivePacketTop nodes hne : ℝ) ^ k *
        normalizedFinitePacketMoment
          (fun x : {x // x ∈ nodes} => c x) (fun x => (x : ℝ))
          (finitePositivePacketTop nodes hne) k := by
  rw [finitePositivePacketMoment, normalizedFinitePacketMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hxmem
  have htopne : (finitePositivePacketTop nodes hne : ℝ) ≠ 0 :=
    (finitePositivePacketTop_pos nodes hne hx).ne'
  rw [div_pow]
  field_simp [htopne]

theorem eventually_finitePositivePacketMoment_weighted_gap
    (nodes : Finset ℝ) (hne : nodes.Nonempty) (c : ℝ → ℝ)
    (hc : ∀ x ∈ nodes, 0 < c x) (hx : ∀ x ∈ nodes, 0 < x) :
    ∀ᶠ k : ℕ in atTop,
      (((2 * k : ℕ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ)) *
          (finitePositivePacketMoment nodes c k *
            finitePositivePacketMoment nodes c (k + 2)) <
        (((2 * k + 2 : ℕ) : ℝ) * ((2 * k + 3 : ℕ) : ℝ)) *
          finitePositivePacketMoment nodes c (k + 1) ^ 2 := by
  let i₀ := finitePositivePacketTop nodes hne
  let c' : {x // x ∈ nodes} → ℝ := fun x => c x
  let x' : {x // x ∈ nodes} → ℝ := fun x => (x : ℝ)
  have hc' : ∀ i, 0 < c' i := fun i => hc i i.property
  have hx' : ∀ i, 0 < x' i := fun i => hx i i.property
  have hmax' : ∀ i, i ≠ i₀ → x' i < x' i₀ := by
    intro i hi
    exact finitePositivePacket_lt_top_of_ne nodes hne hi
  have hnorm := eventually_normalizedFinitePacketMoment_weighted_gap
    c' x' i₀ hc' hx' hmax'
  filter_upwards [hnorm] with k hk
  let R : ℝ := finitePositivePacketTop nodes hne
  let A : ℕ → ℝ := normalizedFinitePacketMoment c' x' i₀
  have hR : 0 < R := finitePositivePacketTop_pos nodes hne hx
  have hRpow : 0 < R ^ (2 * k + 2) := pow_pos hR _
  have hscaled := mul_lt_mul_of_pos_left hk hRpow
  have hMk : finitePositivePacketMoment nodes c k = R ^ k * A k := by
    simpa [R, A, c', x', i₀] using
      finitePositivePacketMoment_eq_top_pow_mul_normalized nodes hne c k hx
  have hMk1 : finitePositivePacketMoment nodes c (k + 1) = R ^ (k + 1) * A (k + 1) := by
    simpa [R, A, c', x', i₀] using
      finitePositivePacketMoment_eq_top_pow_mul_normalized nodes hne c (k + 1) hx
  have hMk2 : finitePositivePacketMoment nodes c (k + 2) = R ^ (k + 2) * A (k + 2) := by
    simpa [R, A, c', x', i₀] using
      finitePositivePacketMoment_eq_top_pow_mul_normalized nodes hne c (k + 2) hx
  rw [hMk, hMk1, hMk2]
  have hp02 : R ^ k * R ^ (k + 2) = R ^ (2 * k + 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hp11 : (R ^ (k + 1)) ^ 2 = R ^ (2 * k + 2) := by
    rw [← pow_mul]
    congr 1
    omega
  calc
    (((2 * k : ℕ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ)) *
          ((R ^ k * A k) * (R ^ (k + 2) * A (k + 2))) =
        R ^ (2 * k + 2) *
          ((((2 * k : ℕ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ)) *
            (A k * A (k + 2))) := by
      rw [← hp02]
      ring
    _ < R ^ (2 * k + 2) *
          ((((2 * k + 2 : ℕ) : ℝ) * ((2 * k + 3 : ℕ) : ℝ)) *
            A (k + 1) ^ 2) := by
      simpa [A] using hscaled
    _ = (((2 * k + 2 : ℕ) : ℝ) * ((2 * k + 3 : ℕ) : ℝ)) *
          (R ^ (k + 1) * A (k + 1)) ^ 2 := by
      rw [mul_pow, hp11]
      ring

theorem halfTurnRepaired_det_neg_of_weighted_gap
    (M : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k)
    (hgap :
      (((2 * k : ℕ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ)) * (M k * M (k + 2)) <
        (((2 * k + 2 : ℕ) : ℝ) * ((2 * k + 3 : ℕ) : ℝ)) * M (k + 1) ^ 2) :
    M k / (Nat.factorial (2 * k - 1) : ℝ) *
          (M (k + 2) / (Nat.factorial (2 * (k + 2) - 1) : ℝ)) -
        (M (k + 1) / (Nat.factorial (2 * (k + 1) - 1) : ℝ)) ^ 2 < 0 := by
  have hstep0 : Nat.factorial (2 * k) =
      (2 * k) * Nat.factorial (2 * k - 1) := by
    have harg : 2 * k - 1 + 1 = 2 * k := by omega
    simpa only [harg] using Nat.factorial_succ (2 * k - 1)
  have hf1Nat : Nat.factorial (2 * k + 1) =
      (2 * k + 1) * (2 * k) * Nat.factorial (2 * k - 1) := by
    simp only [Nat.factorial_succ, hstep0, mul_assoc]
  have hf2Nat : Nat.factorial (2 * k + 3) =
      (2 * k + 3) * (2 * k + 2) * Nat.factorial (2 * k + 1) := by
    simp only [Nat.factorial_succ, mul_assoc]
  have hf1 : (Nat.factorial (2 * k + 1) : ℝ) =
      (((2 * k + 1 : ℕ) : ℝ) * ((2 * k : ℕ) : ℝ)) *
        (Nat.factorial (2 * k - 1) : ℝ) := by
    exact_mod_cast hf1Nat
  have hf2 : (Nat.factorial (2 * k + 3) : ℝ) =
      (((2 * k + 3 : ℕ) : ℝ) * ((2 * k + 2 : ℕ) : ℝ)) *
        (Nat.factorial (2 * k + 1) : ℝ) := by
    exact_mod_cast hf2Nat
  have hF0 : 0 < (Nat.factorial (2 * k - 1) : ℝ) := by positivity
  have hF1 : 0 < (Nat.factorial (2 * k + 1) : ℝ) := by positivity
  have hF2 : 0 < (Nat.factorial (2 * k + 3) : ℝ) := by positivity
  let a : ℝ := ((2 * k : ℕ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hscaled := mul_lt_mul_of_pos_left hgap (mul_pos ha (sq_pos_of_pos hF0))
  have hleftEq :
      (Nat.factorial (2 * k + 1) : ℝ) ^ 2 * (M k * M (k + 2)) =
        a * (Nat.factorial (2 * k - 1) : ℝ) ^ 2 *
          ((((2 * k : ℕ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ)) *
            (M k * M (k + 2))) := by
    rw [hf1]
    dsimp [a]
    ring
  have hrightEq :
      ((Nat.factorial (2 * k - 1) : ℝ) *
          (Nat.factorial (2 * k + 3) : ℝ)) * M (k + 1) ^ 2 =
        a * (Nat.factorial (2 * k - 1) : ℝ) ^ 2 *
          ((((2 * k + 2 : ℕ) : ℝ) * ((2 * k + 3 : ℕ) : ℝ)) *
            M (k + 1) ^ 2) := by
    rw [hf2, hf1]
    dsimp [a]
    ring
  have hratioF :
      (Nat.factorial (2 * k + 1) : ℝ) ^ 2 * (M k * M (k + 2)) <
        ((Nat.factorial (2 * k - 1) : ℝ) *
          (Nat.factorial (2 * k + 3) : ℝ)) * M (k + 1) ^ 2 := by
    rw [hleftEq, hrightEq]
    exact hscaled
  have hdiv :
      (M k * M (k + 2)) /
          ((Nat.factorial (2 * k - 1) : ℝ) *
            (Nat.factorial (2 * k + 3) : ℝ)) <
        M (k + 1) ^ 2 / (Nat.factorial (2 * k + 1) : ℝ) ^ 2 :=
    (div_lt_div_iff₀ (mul_pos hF0 hF2) (sq_pos_of_pos hF1)).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hratioF)
  simp only [show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
    show 2 * (k + 2) - 1 = 2 * k + 3 by omega]
  calc
    M k / (Nat.factorial (2 * k - 1) : ℝ) *
          (M (k + 2) / (Nat.factorial (2 * k + 3) : ℝ)) -
        (M (k + 1) / (Nat.factorial (2 * k + 1) : ℝ)) ^ 2 =
      (M k * M (k + 2)) /
          ((Nat.factorial (2 * k - 1) : ℝ) *
            (Nat.factorial (2 * k + 3) : ℝ)) -
        M (k + 1) ^ 2 / (Nat.factorial (2 * k + 1) : ℝ) ^ 2 := by ring
    _ < 0 := sub_neg.mpr hdiv

theorem finitePositivePacket_halfTurn_det_eventually_neg
    (nodes : Finset ℝ) (hne : nodes.Nonempty) (c : ℝ → ℝ)
    (hc : ∀ x ∈ nodes, 0 < c x) (hx : ∀ x ∈ nodes, 0 < x) :
    ∀ᶠ k : ℕ in atTop,
      halfTurnRepairedPacketMoment nodes c k *
          halfTurnRepairedPacketMoment nodes c (k + 2) -
        halfTurnRepairedPacketMoment nodes c (k + 1) ^ 2 < 0 := by
  have hgap := eventually_finitePositivePacketMoment_weighted_gap nodes hne c hc hx
  have hkpos : ∀ᶠ k : ℕ in atTop, 1 ≤ k := eventually_atTop.2 ⟨1, fun _ hk => hk⟩
  filter_upwards [hgap, hkpos] with k hgapk hk
  simpa [halfTurnRepairedPacketMoment] using
    halfTurnRepaired_det_neg_of_weighted_gap
      (finitePositivePacketMoment nodes c) hk hgapk

theorem finitePositivePacket_halfTurn_not_stieltjes
    (nodes : Finset ℝ) (hne : nodes.Nonempty) (c : ℝ → ℝ)
    (hc : ∀ x ∈ nodes, 0 < c x) (hx : ∀ x ∈ nodes, 0 < x) :
    ¬ ∃ μ : MeasureTheory.Measure ℝ, MeasureTheory.IsFiniteMeasure μ ∧
      HasStieltjesMoments (fun n => halfTurnRepairedPacketMoment nodes c (n + 1)) μ := by
  intro hrep
  obtain ⟨μ, _hfinite, hmoment⟩ := hrep
  have hbad := finitePositivePacket_halfTurn_det_eventually_neg nodes hne c hc hx
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbad
  have hneg := hN (N + 1) (Nat.le_add_right N 1)
  have hnonneg := adjacentHankel_nonneg_of_hasStieltjesMoments hmoment N
  have hN2 : N + 1 + 1 = N + 2 := by omega
  have hN3a : N + 2 + 1 = N + 3 := by omega
  have hN3b : N + 1 + 2 = N + 3 := by omega
  have hnonneg' : 0 ≤
      halfTurnRepairedPacketMoment nodes c (N + 1) *
          halfTurnRepairedPacketMoment nodes c (N + 3) -
        halfTurnRepairedPacketMoment nodes c (N + 2) ^ 2 := by
    simpa only [hN2, hN3a] using hnonneg
  have hneg' :
      halfTurnRepairedPacketMoment nodes c (N + 1) *
          halfTurnRepairedPacketMoment nodes c (N + 3) -
        halfTurnRepairedPacketMoment nodes c (N + 2) ^ 2 < 0 := by
    simpa only [hN2, hN3b] using hneg
  exact (not_lt_of_ge hnonneg') hneg'

end

end GaloisForLFunctions.HTGeometry
