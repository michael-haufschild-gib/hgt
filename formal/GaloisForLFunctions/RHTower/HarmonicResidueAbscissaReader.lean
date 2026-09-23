import GaloisForLFunctions.RHTower.PrimeZetaLogAsymptotic
import GaloisForLFunctions.HTGeometry.CofinalUnitProfileResidue

/-!
# Reading the harmonic residue at the abscissa

A prime field with harmonic residue `c` has prime Dirichlet series

`A(s) = ∑_p a(p) · p^(-(s-1))`,

shifted so that the harmonic field itself sits exactly at the abscissa.  Splitting `a` into `c/p` and
a summable remainder turns `A` into `c · P(s)` plus a term that is *uniformly* bounded on `s ≥ 1`,
because `p^(-(s-1)) ≤ 1` there.  Since the prime zeta function satisfies `P(s) + log(s-1) → const`,
dividing by `-log(s-1)` kills the remainder and normalises `P` to one:

`A(s) / (-log(s-1)) → c`.

So the residue read by bounded cofinal averaging is also the normalised boundary value of a Dirichlet
series.  The two computations share no ingredient: one uses unit reference mass and escaping supports,
the other the pole of `ζ` through the prime zeta function.
-/

open Filter Topology Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The abscissa reader -/

/-- Prime Dirichlet series of a prime field, shifted so that the harmonic field sits at the
abscissa. -/
def primeAbscissaSeries (a : Nat.Primes → ℂ) (s : ℝ) : ℂ :=
  ∑' p : Nat.Primes, a p * ((((p : ℕ) : ℝ) ^ (-(s - 1)) : ℝ) : ℂ)

/-- The normalising logarithm at the abscissa. -/
def abscissaLog (s : ℝ) : ℝ := -Real.log (s - 1)

theorem abscissaShift_le_one {s : ℝ} (hs : 1 ≤ s) (p : Nat.Primes) :
    ((p : ℕ) : ℝ) ^ (-(s - 1)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast p.2.one_lt.le) (by linarith)

theorem abscissaShift_pos (s : ℝ) (p : Nat.Primes) :
    0 < ((p : ℕ) : ℝ) ^ (-(s - 1)) :=
  Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _

theorem primeHarmonicWeight_mul_abscissaShift (s : ℝ) (p : Nat.Primes) :
    primeHarmonicWeight p * ((p : ℕ) : ℝ) ^ (-(s - 1)) =
      ((p : ℕ) : ℝ) ^ (-s) := by
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  rw [primeHarmonicWeight, ← Real.rpow_neg_one ((p : ℕ) : ℝ), ← Real.rpow_add hp]
  congr 1
  ring

/-! ## The normalising logarithm -/

theorem tendsto_abscissaLog_atTop :
    Tendsto abscissaLog (nhdsWithin 1 (Ioi 1)) atTop := by
  refine tendsto_atTop.mpr fun M => ?_
  have hmem : Iio (1 + Real.exp (-M)) ∈ nhds (1 : ℝ) :=
    Iio_mem_nhds (by linarith [Real.exp_pos (-M)])
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hmem] with s hs1 hs2
  have h1 : 0 < s - 1 := by
    have hlt : (1 : ℝ) < s := hs1
    linarith
  have h2 : s - 1 < Real.exp (-M) := by
    have hlt : s < 1 + Real.exp (-M) := hs2
    linarith
  rw [abscissaLog, le_neg]
  calc Real.log (s - 1) ≤ Real.log (Real.exp (-M)) := Real.log_le_log h1 h2.le
    _ = -M := Real.log_exp _

/-- **The prime zeta function normalises to one at the abscissa.** -/
theorem tendsto_primeZeta_div_abscissaLog :
    Tendsto (fun s => primeZeta s / abscissaLog s) (nhdsWithin 1 (Ioi 1))
      (nhds 1) := by
  have hL := tendsto_abscissaLog_atTop
  have hd : Tendsto (fun s => (primeZeta s + Real.log (s - 1)) / abscissaLog s)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) :=
    tendsto_primeZeta_add_log_sub.div_atTop hL
  have hone : Tendsto
      (fun s => (primeZeta s + Real.log (s - 1)) / abscissaLog s + 1)
      (nhdsWithin 1 (Ioi 1)) (nhds (0 + 1)) := hd.add tendsto_const_nhds
  rw [zero_add] at hone
  refine hone.congr' ?_
  filter_upwards [hL.eventually_ge_atTop 1] with s hs
  have hlog : Real.log (s - 1) ≠ 0 := by
    intro h
    rw [abscissaLog, h, neg_zero] at hs
    norm_num at hs
  rw [abscissaLog]
  field_simp
  ring

/-! ## Splitting the series -/

section Reader

variable {a : Nat.Primes → ℂ} {c : ℂ}

/-- The remainder series of the abscissa reader. -/
def primeAbscissaRemainder (a : Nat.Primes → ℂ) (c : ℂ) (s : ℝ) : ℂ :=
  ∑' p : Nat.Primes, (a p - c * (primeHarmonicWeight p : ℂ)) *
    ((((p : ℕ) : ℝ) ^ (-(s - 1)) : ℝ) : ℂ)

theorem summable_primeAbscissaRemainderTerm
    (hres : HasReferenceResidue primeHarmonicWeight a c) {s : ℝ} (hs : 1 ≤ s) :
    Summable fun p : Nat.Primes =>
      (a p - c * (primeHarmonicWeight p : ℂ)) *
        ((((p : ℕ) : ℝ) ^ (-(s - 1)) : ℝ) : ℂ) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _)
    (fun p => ?_) (Summable.norm hres))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (abscissaShift_pos s p)]
  exact mul_le_of_le_one_right (norm_nonneg _) (abscissaShift_le_one hs p)

/-- The remainder is bounded by the total mass of the summable part, uniformly at
and above the abscissa. -/
theorem norm_primeAbscissaRemainder_le
    (hres : HasReferenceResidue primeHarmonicWeight a c) {s : ℝ} (hs : 1 ≤ s) :
    ‖primeAbscissaRemainder a c s‖ ≤
      ∑' p : Nat.Primes, ‖a p - c * (primeHarmonicWeight p : ℂ)‖ := by
  have hterm := summable_primeAbscissaRemainderTerm hres hs
  refine le_trans (norm_tsum_le_tsum_norm (Summable.norm hterm)) ?_
  refine Summable.tsum_le_tsum (fun p => ?_) (Summable.norm hterm)
    (Summable.norm hres)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (abscissaShift_pos s p)]
  exact mul_le_of_le_one_right (norm_nonneg _) (abscissaShift_le_one hs p)

theorem primeAbscissaSeries_eq
    (hres : HasReferenceResidue primeHarmonicWeight a c) {s : ℝ} (hs : 1 < s) :
    primeAbscissaSeries a s =
      c * ((primeZeta s : ℝ) : ℂ) + primeAbscissaRemainder a c s := by
  have hZ : HasSum (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-s)) (primeZeta s) :=
    (summable_primeZetaTerm hs).hasSum
  have h1 : HasSum
      (fun p : Nat.Primes => c * ((((p : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))
      (c * ((primeZeta s : ℝ) : ℂ)) :=
    (Complex.hasSum_ofReal.mpr hZ).mul_left c
  have h2 := (summable_primeAbscissaRemainderTerm hres hs.le).hasSum
  refine ((h1.add h2).congr_fun fun p => ?_).tsum_eq
  have hharm : ((((p : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) =
      ((primeHarmonicWeight p : ℝ) : ℂ) *
        ((((p : ℕ) : ℝ) ^ (-(s - 1)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, primeHarmonicWeight_mul_abscissaShift]
  rw [hharm]
  ring

theorem summable_primeAbscissaTermOfResidue
    (hres : HasReferenceResidue primeHarmonicWeight a c) {s : ℝ} (hs : 1 < s) :
    Summable fun p : Nat.Primes =>
      a p * ((((p : ℕ) : ℝ) ^ (-(s - 1)) : ℝ) : ℂ) := by
  have hZ : HasSum (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-s)) (primeZeta s) :=
    (summable_primeZetaTerm hs).hasSum
  have h1 : Summable fun p : Nat.Primes =>
      c * ((((p : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) :=
    ((Complex.hasSum_ofReal.mpr hZ).mul_left c).summable
  have h2 := summable_primeAbscissaRemainderTerm hres hs.le
  refine (h1.add h2).congr fun p => ?_
  have hharm : ((((p : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) =
      ((primeHarmonicWeight p : ℝ) : ℂ) *
        ((((p : ℕ) : ℝ) ^ (-(s - 1)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, primeHarmonicWeight_mul_abscissaShift]
  rw [hharm]
  ring

/-- **Effective form of the reader.**  At a single height the deviation of the
normalised series from the residue is bounded explicitly, by the prime zeta
defect against the normaliser and the total mass of the summable part. -/
theorem norm_primeAbscissaSeries_div_sub_residue_le
    (hres : HasReferenceResidue primeHarmonicWeight a c) {s : ℝ} (hs : 1 < s)
    (hL : 0 < abscissaLog s) :
    ‖primeAbscissaSeries a s / ((abscissaLog s : ℝ) : ℂ) - c‖ ≤
      (‖c‖ * |primeZeta s - abscissaLog s| +
        ∑' p : Nat.Primes, ‖a p - c * (primeHarmonicWeight p : ℂ)‖) /
        abscissaLog s := by
  have hLne : ((abscissaLog s : ℝ) : ℂ) ≠ 0 := by simpa using hL.ne'
  have hkey : primeAbscissaSeries a s / ((abscissaLog s : ℝ) : ℂ) - c =
      (c * (((primeZeta s - abscissaLog s : ℝ)) : ℂ) +
        primeAbscissaRemainder a c s) / ((abscissaLog s : ℝ) : ℂ) := by
    rw [primeAbscissaSeries_eq hres hs]
    push_cast
    field_simp
    ring
  rw [hkey, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  refine div_le_div_of_nonneg_right ?_ hL.le
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖c * (((primeZeta s - abscissaLog s : ℝ)) : ℂ)‖ =
      ‖c‖ * |primeZeta s - abscissaLog s| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 := norm_primeAbscissaRemainder_le hres hs.le
  rw [h1]
  linarith

/-- The matching lower bound: past an explicit height the reading cannot fall far
below the modulus of the residue. -/
theorem le_norm_primeAbscissaSeries_div
    (hres : HasReferenceResidue primeHarmonicWeight a c) {s : ℝ} (hs : 1 < s)
    (hL : 0 < abscissaLog s) :
    ‖c‖ - (‖c‖ * |primeZeta s - abscissaLog s| +
        ∑' p : Nat.Primes, ‖a p - c * (primeHarmonicWeight p : ℂ)‖) /
          abscissaLog s ≤
      ‖primeAbscissaSeries a s / ((abscissaLog s : ℝ) : ℂ)‖ := by
  have hdev := norm_primeAbscissaSeries_div_sub_residue_le hres hs hL
  have htri : ‖c‖ ≤ ‖primeAbscissaSeries a s / ((abscissaLog s : ℝ) : ℂ)‖ +
      ‖primeAbscissaSeries a s / ((abscissaLog s : ℝ) : ℂ) - c‖ := by
    have h := norm_sub_le (primeAbscissaSeries a s / ((abscissaLog s : ℝ) : ℂ))
      (primeAbscissaSeries a s / ((abscissaLog s : ℝ) : ℂ) - c)
    simpa using h
  linarith

/-- **Effective height bound at a unit residue.**  If the residue has modulus one
and the normalised series drops below `r < 1` at some height, that height is
bounded explicitly: the normaliser cannot yet have grown past
`(defect + mass) / (1 - r)`.  This is the analytic counterpart of the
finite-depth grade bound on the profile side. -/
theorem abscissaLog_le_of_norm_div_le
    (hres : HasReferenceResidue primeHarmonicWeight a c) (hc : ‖c‖ = 1)
    {s r : ℝ} (hs : 1 < s) (hL : 0 < abscissaLog s) (hr : r < 1)
    (hbound : ‖primeAbscissaSeries a s / ((abscissaLog s : ℝ) : ℂ)‖ ≤ r) :
    abscissaLog s ≤
      (|primeZeta s - abscissaLog s| +
        ∑' p : Nat.Primes, ‖a p - c * (primeHarmonicWeight p : ℂ)‖) / (1 - r) := by
  have hdev := norm_primeAbscissaSeries_div_sub_residue_le hres hs hL
  rw [hc, one_mul] at hdev
  have hlow : (1 : ℝ) - r ≤
      ‖primeAbscissaSeries a s / ((abscissaLog s : ℝ) : ℂ) - c‖ := by
    have htri : ‖c‖ ≤
        ‖primeAbscissaSeries a s / ((abscissaLog s : ℝ) : ℂ)‖ +
          ‖primeAbscissaSeries a s / ((abscissaLog s : ℝ) : ℂ) - c‖ := by
      have h := norm_sub_le (primeAbscissaSeries a s / ((abscissaLog s : ℝ) : ℂ))
        (primeAbscissaSeries a s / ((abscissaLog s : ℝ) : ℂ) - c)
      simpa using h
    rw [hc] at htri
    linarith
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - r)]
  have hmul := mul_le_mul_of_nonneg_left (le_trans hlow hdev) hL.le
  calc abscissaLog s * (1 - r) ≤
        abscissaLog s *
          ((|primeZeta s - abscissaLog s| +
            ∑' p : Nat.Primes,
              ‖a p - c * (primeHarmonicWeight p : ℂ)‖) / abscissaLog s) := hmul
    _ = |primeZeta s - abscissaLog s| +
          ∑' p : Nat.Primes, ‖a p - c * (primeHarmonicWeight p : ℂ)‖ := by
        field_simp

/-! ## The reader law -/

/-- **The harmonic residue is the normalised boundary value of the prime Dirichlet
series.**  Together with `tendsto_profileAverage` this gives two independent
formulas for one invariant. -/
theorem tendsto_primeAbscissaSeries_div_abscissaLog
    (hres : HasReferenceResidue primeHarmonicWeight a c) :
    Tendsto (fun s => primeAbscissaSeries a s / ((abscissaLog s : ℝ) : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds c) := by
  have hL := tendsto_abscissaLog_atTop
  set M : ℝ := ∑' p : Nat.Primes, ‖a p - c * (primeHarmonicWeight p : ℂ)‖ with hM
  have hrem : Tendsto
      (fun s => primeAbscissaRemainder a c s / ((abscissaLog s : ℝ) : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    have hMdiv : Tendsto (fun s => M / abscissaLog s) (nhdsWithin 1 (Ioi 1))
        (nhds 0) := tendsto_const_nhds.div_atTop hL
    filter_upwards [self_mem_nhdsWithin, hL.eventually_ge_atTop 1,
      hMdiv.eventually (gt_mem_nhds hε)] with s hs1 hs2 hs3
    have hsle : (1 : ℝ) ≤ s := le_of_lt hs1
    have hLpos : 0 < abscissaLog s := by linarith
    have hbound := norm_primeAbscissaRemainder_le hres hsle
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLpos]
    calc ‖primeAbscissaRemainder a c s‖ / abscissaLog s ≤ M / abscissaLog s :=
          div_le_div_of_nonneg_right hbound hLpos.le
      _ < ε := hs3
  have hzeta : Tendsto
      (fun s => ((primeZeta s / abscissaLog s : ℝ) : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds ((1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp tendsto_primeZeta_div_abscissaLog
  have hsum : Tendsto
      (fun s => c * ((primeZeta s / abscissaLog s : ℝ) : ℂ) +
        primeAbscissaRemainder a c s / ((abscissaLog s : ℝ) : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds (c * ((1 : ℝ) : ℂ) + 0)) :=
    (hzeta.const_mul c).add hrem
  have hval : c * ((1 : ℝ) : ℂ) + 0 = c := by norm_num
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hL.eventually_ge_atTop 1] with s hs1 hs2
  have hslt : (1 : ℝ) < s := hs1
  have hLne : ((abscissaLog s : ℝ) : ℂ) ≠ 0 := by
    have hLpos : 0 < abscissaLog s := by linarith
    simpa using hLpos.ne'
  rw [primeAbscissaSeries_eq hres hslt, add_div, Complex.ofReal_div]
  ring_nf

end Reader

/-! ## The enlarged domain: negligible fields are also invisible here -/

section Negligible

variable {b : Nat.Primes → ℂ}

theorem summable_primeAbscissaNegligibleNorm
    (hb : IsCofinitelyNegligible primeHarmonicWeight b) {ε : ℝ} (hε : 0 < ε)
    {s : ℝ} (hs : 1 < s) :
    Summable fun p : Nat.Primes => ‖b p‖ * ((p : ℕ) : ℝ) ^ (-(s - 1)) := by
  obtain ⟨s₀, hfin, hs₀⟩ := hb ε hε
  have hgsum : Summable (Set.indicator s₀ fun q : Nat.Primes => ‖b q‖) :=
    summable_of_hasFiniteSupport (hfin.subset Set.support_indicator_subset)
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_)
    (((summable_primeZetaTerm hs).mul_left ε).add hgsum)
  by_cases hp : p ∈ s₀
  · rw [Set.indicator_of_mem hp]
    have h1 : ‖b p‖ * ((p : ℕ) : ℝ) ^ (-(s - 1)) ≤ ‖b p‖ :=
      mul_le_of_le_one_right (norm_nonneg _) (abscissaShift_le_one hs.le p)
    have h2 : (0 : ℝ) ≤ ε * ((p : ℕ) : ℝ) ^ (-s) := by positivity
    linarith
  · rw [Set.indicator_of_notMem hp]
    have hbound := mul_le_mul_of_nonneg_right (hs₀ p hp)
      (abscissaShift_pos s p).le
    have hharm : ε * primeHarmonicWeight p * ((p : ℕ) : ℝ) ^ (-(s - 1)) =
        ε * ((p : ℕ) : ℝ) ^ (-s) := by
      rw [mul_assoc, primeHarmonicWeight_mul_abscissaShift]
    nlinarith [hbound, hharm]

theorem summable_primeAbscissaTermOfNegligible
    (hb : IsCofinitelyNegligible primeHarmonicWeight b) {s : ℝ} (hs : 1 < s) :
    Summable fun p : Nat.Primes =>
      b p * ((((p : ℕ) : ℝ) ^ (-(s - 1)) : ℝ) : ℂ) := by
  refine Summable.of_norm
    ((summable_primeAbscissaNegligibleNorm hb (ε := 1) one_pos hs).congr
      fun p => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (abscissaShift_pos s p)]

theorem norm_primeAbscissaSeries_negligible_le
    (hb : IsCofinitelyNegligible primeHarmonicWeight b) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 < t →
      ‖primeAbscissaSeries b t‖ ≤ ε * primeZeta t + C := by
  obtain ⟨s₀, hfin, hs₀⟩ := hb ε hε
  have hgsum : Summable (Set.indicator s₀ fun q : Nat.Primes => ‖b q‖) :=
    summable_of_hasFiniteSupport (hfin.subset Set.support_indicator_subset)
  refine ⟨∑' p : Nat.Primes, Set.indicator s₀ (fun q : Nat.Primes => ‖b q‖) p,
    tsum_nonneg fun p => ?_, fun t ht => ?_⟩
  · by_cases hp : p ∈ s₀
    · rw [Set.indicator_of_mem hp]; exact norm_nonneg _
    · rw [Set.indicator_of_notMem hp]
  · have hmaj : ∀ p : Nat.Primes,
        ‖b p‖ * ((p : ℕ) : ℝ) ^ (-(t - 1)) ≤
          ε * ((p : ℕ) : ℝ) ^ (-t) +
            Set.indicator s₀ (fun q : Nat.Primes => ‖b q‖) p := by
      intro p
      by_cases hp : p ∈ s₀
      · rw [Set.indicator_of_mem hp]
        have h1 : ‖b p‖ * ((p : ℕ) : ℝ) ^ (-(t - 1)) ≤ ‖b p‖ :=
          mul_le_of_le_one_right (norm_nonneg _) (abscissaShift_le_one ht.le p)
        have h2 : (0 : ℝ) ≤ ε * ((p : ℕ) : ℝ) ^ (-t) := by positivity
        linarith
      · rw [Set.indicator_of_notMem hp]
        have hbound := mul_le_mul_of_nonneg_right (hs₀ p hp)
          (abscissaShift_pos t p).le
        have hharm : ε * primeHarmonicWeight p * ((p : ℕ) : ℝ) ^ (-(t - 1)) =
            ε * ((p : ℕ) : ℝ) ^ (-t) := by
          rw [mul_assoc, primeHarmonicWeight_mul_abscissaShift]
        nlinarith [hbound, hharm]
    have hnormSum := summable_primeAbscissaNegligibleNorm hb hε ht
    have hterm : Summable fun p : Nat.Primes =>
        b p * ((((p : ℕ) : ℝ) ^ (-(t - 1)) : ℝ) : ℂ) := by
      refine Summable.of_norm (hnormSum.congr fun p => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (abscissaShift_pos t p)]
    have hZ : HasSum (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-t)) (primeZeta t) :=
      (summable_primeZetaTerm ht).hasSum
    calc ‖primeAbscissaSeries b t‖
        ≤ ∑' p : Nat.Primes, ‖b p * ((((p : ℕ) : ℝ) ^ (-(t - 1)) : ℝ) : ℂ)‖ :=
          norm_tsum_le_tsum_norm (Summable.norm hterm)
      _ = ∑' p : Nat.Primes, ‖b p‖ * ((p : ℕ) : ℝ) ^ (-(t - 1)) :=
          tsum_congr fun p => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (abscissaShift_pos t p)]
      _ ≤ ∑' p : Nat.Primes, (ε * ((p : ℕ) : ℝ) ^ (-t) +
            Set.indicator s₀ (fun q : Nat.Primes => ‖b q‖) p) :=
          hnormSum.tsum_le_tsum hmaj
            (((summable_primeZetaTerm ht).mul_left ε).add hgsum)
      _ = ε * primeZeta t +
            ∑' p : Nat.Primes,
              Set.indicator s₀ (fun q : Nat.Primes => ‖b q‖) p := by
          rw [Summable.tsum_add ((summable_primeZetaTerm ht).mul_left ε) hgsum,
            tsum_mul_left, hZ.tsum_eq]

/-- **Negligible fields are invisible to the abscissa reader too.**  Off a finite
set the field is `ε`-small relative to `1/p`, so its series is at most
`ε · P(s) + O(1)`, and `P(s) / (-log(s-1)) → 1` absorbs the `ε`. -/
theorem tendsto_primeAbscissaSeries_div_abscissaLog_of_negligible
    (hb : IsCofinitelyNegligible primeHarmonicWeight b) :
    Tendsto (fun s => primeAbscissaSeries b s / ((abscissaLog s : ℝ) : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  have hL := tendsto_abscissaLog_atTop
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨C, hC0, hCbound⟩ :=
    norm_primeAbscissaSeries_negligible_le hb (by positivity : 0 < ε / 4)
  have hratio : ∀ᶠ s in nhdsWithin 1 (Ioi 1), primeZeta s / abscissaLog s < 2 :=
    tendsto_primeZeta_div_abscissaLog.eventually (gt_mem_nhds (by norm_num))
  have hCdiv : ∀ᶠ s in nhdsWithin 1 (Ioi 1), C / abscissaLog s < ε / 2 :=
    (tendsto_const_nhds.div_atTop hL).eventually
      (gt_mem_nhds (by positivity))
  filter_upwards [self_mem_nhdsWithin, hL.eventually_ge_atTop 1, hratio, hCdiv]
    with s hs1 hs2 hs3 hs4
  have hslt : (1 : ℝ) < s := hs1
  have hLpos : 0 < abscissaLog s := by linarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLpos]
  have hnum := hCbound s hslt
  have hstep : ‖primeAbscissaSeries b s‖ / abscissaLog s ≤
      ε / 4 * (primeZeta s / abscissaLog s) + C / abscissaLog s := by
    rw [div_le_iff₀ hLpos]
    have hexp : (ε / 4 * (primeZeta s / abscissaLog s) + C / abscissaLog s) *
        abscissaLog s = ε / 4 * primeZeta s + C := by
      field_simp
    rw [hexp]
    exact hnum
  have hfinal : ε / 4 * (primeZeta s / abscissaLog s) + C / abscissaLog s < ε := by
    have h1 : ε / 4 * (primeZeta s / abscissaLog s) < ε / 4 * 2 :=
      mul_lt_mul_of_pos_left hs3 (by positivity)
    linarith
  linarith

/-- The abscissa reader also computes the residue on the enlarged domain
`ell^(1 : ℕ) + negligible`. -/
theorem tendsto_primeAbscissaSeries_div_abscissaLog_mod
    {a : Nat.Primes → ℂ} {c : ℂ}
    (hres : HasReferenceResidueMod primeHarmonicWeight a c) :
    Tendsto (fun s => primeAbscissaSeries a s / ((abscissaLog s : ℝ) : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds c) := by
  obtain ⟨b₁, b₂, hb₁, hb₂, hdec⟩ := hres
  have h1 : HasReferenceResidue primeHarmonicWeight (fun p => c *
      (primeHarmonicWeight p : ℂ) + b₁ p) c := by
    refine hb₁.congr fun p => ?_
    ring
  have hsplit : ∀ s : ℝ, 1 < s →
      primeAbscissaSeries a s =
        primeAbscissaSeries (fun p => c * (primeHarmonicWeight p : ℂ) + b₁ p) s +
          primeAbscissaSeries b₂ s := by
    intro s hs
    have hA := (summable_primeAbscissaTermOfResidue h1 hs).hasSum
    have hB := (summable_primeAbscissaTermOfNegligible hb₂ hs).hasSum
    refine ((hA.add hB).congr_fun fun p => ?_).tsum_eq
    have hap : a p = (c * (primeHarmonicWeight p : ℂ) + b₁ p) + b₂ p := by
      have := hdec p
      linear_combination this
    rw [hap]
    ring
  have hlim1 := tendsto_primeAbscissaSeries_div_abscissaLog h1
  have hlim2 := tendsto_primeAbscissaSeries_div_abscissaLog_of_negligible hb₂
  have hsum : Tendsto
      (fun s =>
        primeAbscissaSeries (fun p => c * (primeHarmonicWeight p : ℂ) + b₁ p) s /
            ((abscissaLog s : ℝ) : ℂ) +
          primeAbscissaSeries b₂ s / ((abscissaLog s : ℝ) : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds (c + 0)) := hlim1.add hlim2
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hslt : (1 : ℝ) < s := hs
  rw [← add_div, hsplit s hslt]

end Negligible

/-! ## One invariant, two readers -/

/-- **Uniqueness of the prime-harmonic residue on the enlarged domain, from the
prime zeta asymptotic alone.**  No averaging profile and no enumeration of the
primes is used; the analytic reader has a limit, and limits are unique. -/
theorem primeHarmonicResidueMod_unique_of_abscissa
    {a : Nat.Primes → ℂ} {c d : ℂ}
    (hc : HasReferenceResidueMod primeHarmonicWeight a c)
    (hd : HasReferenceResidueMod primeHarmonicWeight a d) : c = d :=
  tendsto_nhds_unique (tendsto_primeAbscissaSeries_div_abscissaLog_mod hc)
    (tendsto_primeAbscissaSeries_div_abscissaLog_mod hd)

/-- **Two readers, one invariant.**  Whenever a prime field has a residue over the
prime-harmonic weight, the combinatorial limit of bounded cofinal averages and the
analytic normalised boundary value of its Dirichlet series are the same number.
The two computations share no ingredient: one uses unit reference mass with
escaping supports, the other the pole of `zeta` through the prime zeta
function. -/
theorem tendsto_profileAverage_eq_tendsto_primeAbscissa
    {mu : ℕ → Nat.Primes → ℝ}
    (hmu : IsCofinalUnitProfile primeHarmonicWeight mu)
    {a : Nat.Primes → ℂ} {c d e : ℂ}
    (hres : HasReferenceResidueMod primeHarmonicWeight a e)
    (hprof : Tendsto (fun N => profileAverage mu N a) atTop (nhds c))
    (habs : Tendsto (fun s => primeAbscissaSeries a s / ((abscissaLog s : ℝ) : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds d)) :
    c = d := by
  have hc : c = e :=
    tendsto_nhds_unique hprof
      (tendsto_profileAverage_mod primeHarmonicWeight_nonneg hmu hres)
  have hd : d = e :=
    tendsto_nhds_unique habs
      (tendsto_primeAbscissaSeries_div_abscissaLog_mod hres)
  rw [hc, hd]

end

end RHTower
