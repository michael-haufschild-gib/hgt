import GaloisForLFunctions.RHTower.Sieve.SmoothCount

/-!
# The lower tail of the distinct prime count in an interval

Fibring the integers of `Ioc a b` over their `z`-smooth part turns the count of integers with few
distinct prime factors into a sum of sieve problems:

`#{n ∈ (a,b] : ω n ≤ k} ≤ ∑_{s z-smooth, s ≤ b, ω s ≤ k} #{m ∈ (a/s, b/s] : P⁻(m) > z}`.

Each fibre is exactly the rough-number count bounded by `card_rough_Ioc_le`; the index set is
controlled by `card_smoothUpTo_card_primeFactors_le`, and the weights `1/s` by
`sum_smoothUpTo_card_le_inv_le_exp`.  Combining the three gives the tail bound: a main term
proportional to `(b-a)/log z` times a tilted Euler factor, plus one sieve error per surviving
smooth part.
-/

namespace RHTower.Sieve

open Finset Nat

/-- **Fibring over the smooth part.**  The integers of `Ioc a b` with at most `k` distinct prime
factors are distributed among the rough-number counts of the rescaled intervals. -/
theorem card_omega_le_le_sum (a b z k : ℕ) :
    (#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k})
      ≤ ∑ s ∈ {s ∈ smoothUpTo (Nat.primesLE z) b | s.primeFactors.card ≤ k},
          (#{m ∈ Finset.Ioc (a / s) (b / s) | ∀ p ∈ Nat.primesLE z, ¬ p ∣ m}) := by
  classical
  set A : Finset ℕ := {n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k} with hA
  set T : Finset ℕ := {s ∈ smoothUpTo (Nat.primesLE z) b | s.primeFactors.card ≤ k} with hT
  have hfib : ∀ n ∈ A, smoothPart z n ∈ T := by
    intro n hn
    obtain ⟨hmem, hcard⟩ := Finset.mem_filter.1 hn
    obtain ⟨han, hnb⟩ := Finset.mem_Ioc.1 hmem
    have hn0 : n ≠ 0 := by omega
    have hspos : 0 < smoothPart z n := smoothPart_pos z n
    have hsdvd : smoothPart z n ∣ n := smoothPart_dvd z n
    have hsle : smoothPart z n ≤ b :=
      le_trans (Nat.le_of_dvd (by omega) hsdvd) hnb
    have hsub : (smoothPart z n).primeFactors ⊆ Nat.primesLE z := by
      rw [primeFactors_smoothPart hn0 z]
      intro p hp
      obtain ⟨hpn, hpz⟩ := Finset.mem_filter.1 hp
      exact Nat.mem_primesLE.2 ⟨hpz, Nat.prime_of_mem_primeFactors hpn⟩
    have hscard : (smoothPart z n).primeFactors.card ≤ k := by
      have hsplit := card_primeFactors_roughPart_add hn0 z
      omega
    exact Finset.mem_filter.2 ⟨mem_smoothUpTo.2 ⟨⟨hspos, hsle⟩, hsub⟩, hscard⟩
  rw [Finset.card_eq_sum_card_fiberwise hfib]
  refine Finset.sum_le_sum ?_
  intro σ hσ
  obtain ⟨hσmem, -⟩ := Finset.mem_filter.1 hσ
  obtain ⟨⟨hσ1, hσb⟩, -⟩ := mem_smoothUpTo.1 hσmem
  have hσpos : 0 < σ := hσ1
  refine Finset.card_le_card_of_injOn (fun n => n / σ) ?_ ?_
  · intro n hn
    obtain ⟨hnA, hns⟩ := Finset.mem_filter.1 hn
    obtain ⟨hmem, -⟩ := Finset.mem_filter.1 hnA
    obtain ⟨han, hnb⟩ := Finset.mem_Ioc.1 hmem
    have hn0 : n ≠ 0 := by omega
    have hmul : smoothPart z n * roughPart z n = n := smoothPart_mul_roughPart hn0 z
    have hσdvd : σ ∣ n := hns ▸ smoothPart_dvd z n
    have hn_eq : n = σ * roughPart z n := by
      conv_lhs => rw [← hmul]
      rw [hns]
    have hdiv : n / σ = roughPart z n := by
      conv_lhs => rw [hn_eq]
      exact Nat.mul_div_cancel_left _ hσpos
    have hupper : n / σ ≤ b / σ := Nat.div_le_div_right hnb
    have hlower : a / σ < n / σ := by
      rw [Nat.div_lt_iff_lt_mul hσpos, Nat.div_mul_cancel hσdvd]
      exact han
    refine Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨hlower, hupper⟩, ?_⟩
    intro p hp
    show ¬ p ∣ n / σ
    rw [hdiv]
    exact not_dvd_roughPart hn0 hp
  · intro x hx y hy hxy
    obtain ⟨hxA, hxs⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hx)
    obtain ⟨hyA, hys⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
    have hxdvd : σ ∣ x := hxs ▸ smoothPart_dvd z x
    have hydvd : σ ∣ y := hys ▸ smoothPart_dvd z y
    have hxe : σ * (x / σ) = x := Nat.mul_div_cancel' hxdvd
    have hye : σ * (y / σ) = y := Nat.mul_div_cancel' hydvd
    have : x / σ = y / σ := hxy
    rw [← hxe, ← hye, this]

/-- The per-fibre sieve density: main term plus truncation defect. -/
noncomputable def roughDensityBound (z r : ℕ) (lam : ℝ) : ℝ :=
  Real.exp mertensSecondLowerConst / Real.log z
    + Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / lam ^ r

theorem roughDensityBound_nonneg {z r : ℕ} (hz : 2 ≤ z) {lam : ℝ} (hlam : 1 ≤ lam) :
    0 ≤ roughDensityBound z r lam := by
  have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le zero_lt_one hlam
  unfold roughDensityBound
  have h1 : 0 < Real.exp mertensSecondLowerConst / Real.log z := by positivity
  have h2 : 0 ≤ Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / lam ^ r := by
    have : (0 : ℝ) ≤ (Real.log z) ^ lam := Real.rpow_nonneg hlogz.le lam
    positivity
  linarith

/-- The tilted weight of the surviving smooth parts. -/
noncomputable def smoothTiltBound (z k : ℕ) (t : ℝ) : ℝ :=
  Real.exp (t * (logLog z + mertensSecondUpperConst + 1)) / t ^ k

/-- The number of surviving smooth parts. -/
noncomputable def smoothIndexBound (z b k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), (((Nat.primesLE z).card * Nat.log 2 b).choose j : ℝ)

/-- **Lower-tail bound.**  Integers of `Ioc a b` with at most `k` distinct prime factors are
counted by a sieve main term times a tilted Euler weight, plus one sieve error per surviving
smooth part. -/
theorem card_omega_le_le (a b z k r : ℕ) (hab : a ≤ b) (hz : 2 ≤ z) (hr : Even r)
    {lam : ℝ} (hlam : 1 ≤ lam) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k} : ℝ)
      ≤ ((b : ℝ) - a) * roughDensityBound z r lam * smoothTiltBound z k t
        + (roughDensityBound z r lam + ((truncDivisors (primorial z) r).card : ℝ))
            * smoothIndexBound z b k := by
  classical
  set T : Finset ℕ := {s ∈ smoothUpTo (Nat.primesLE z) b | s.primeFactors.card ≤ k} with hT
  set R : ℝ := roughDensityBound z r lam with hR
  set T₀ : ℝ := ((truncDivisors (primorial z) r).card : ℝ) with hT₀
  have hR0 : 0 ≤ R := roughDensityBound_nonneg hz hlam
  have hT₀0 : 0 ≤ T₀ := by positivity
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hstart : (#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k} : ℝ)
      ≤ ∑ σ ∈ T, ((#{m ∈ Finset.Ioc (a / σ) (b / σ) | ∀ p ∈ Nat.primesLE z, ¬ p ∣ m}) : ℝ) := by
    have := card_omega_le_le_sum a b z k
    exact_mod_cast this
  have hfibre : ∀ σ ∈ T,
      ((#{m ∈ Finset.Ioc (a / σ) (b / σ) | ∀ p ∈ Nat.primesLE z, ¬ p ∣ m}) : ℝ)
        ≤ ((b : ℝ) - a) * R * (1 / σ) + (R + T₀) := by
    intro σ hσ
    obtain ⟨hσmem, -⟩ := Finset.mem_filter.1 hσ
    obtain ⟨⟨hσ1, hσb⟩, -⟩ := mem_smoothUpTo.1 hσmem
    have hσpos : 0 < σ := hσ1
    have hσR : (0 : ℝ) < σ := by exact_mod_cast hσpos
    have hdivle : a / σ ≤ b / σ := Nat.div_le_div_right hab
    have hsieve := card_rough_Ioc_le (z := z) (a := a / σ) (b := b / σ) (r := r) hz hdivle hr hlam
    have hgap : ((b / σ : ℕ) : ℝ) - ((a / σ : ℕ) : ℝ) ≤ ((b : ℝ) - a) / σ + 1 := by
      have hb := (cast_div_bounds (d := σ) (n := b) hσpos).1
      have ha := (cast_div_bounds (d := σ) (n := a) hσpos).2
      have : ((b : ℝ) - a) / σ = (b : ℝ) / σ - (a : ℝ) / σ := by ring
      rw [this]
      linarith
    have hcombine :
        ((b / σ : ℕ) : ℝ) - ((a / σ : ℕ) : ℝ)
            ≤ ((b : ℝ) - a) / σ + 1 := hgap
    have hstep :
        ((#{m ∈ Finset.Ioc (a / σ) (b / σ) | ∀ p ∈ Nat.primesLE z, ¬ p ∣ m}) : ℝ)
          ≤ (((b / σ : ℕ) : ℝ) - ((a / σ : ℕ) : ℝ)) * R + T₀ := by
      have hring : (((b / σ : ℕ) : ℝ) - ((a / σ : ℕ) : ℝ)) * R + T₀
          = (((b / σ : ℕ) : ℝ) - ((a / σ : ℕ) : ℝ))
              * (Real.exp mertensSecondLowerConst / Real.log z)
            + (((b / σ : ℕ) : ℝ) - ((a / σ : ℕ) : ℝ))
                * (Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / lam ^ r)
            + T₀ := by
        rw [hR]
        unfold roughDensityBound
        ring
      rw [hring]
      exact hsieve
    refine le_trans hstep ?_
    have hmul : (((b / σ : ℕ) : ℝ) - ((a / σ : ℕ) : ℝ)) * R
        ≤ (((b : ℝ) - a) / σ + 1) * R := mul_le_mul_of_nonneg_right hcombine hR0
    have hfin : (((b : ℝ) - a) / σ + 1) * R = ((b : ℝ) - a) * R * (1 / σ) + R := by
      field_simp
    linarith [hmul, hfin.le, hfin.ge]
  refine le_trans hstart (le_trans (Finset.sum_le_sum hfibre) ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hsum : ∑ σ ∈ T, (1 : ℝ) / σ ≤ smoothTiltBound z k t := by
    rw [hT]
    exact sum_smoothUpTo_card_le_inv_le_exp ht0 ht1 k hz b
  have hcard : (T.card : ℝ) ≤ smoothIndexBound z b k := by
    rw [hT, smoothIndexBound]
    have := card_smoothUpTo_card_primeFactors_le z b k
    exact_mod_cast this
  have hpos1 : 0 ≤ ((b : ℝ) - a) * R := mul_nonneg hlen hR0
  have h1 : ((b : ℝ) - a) * R * ∑ σ ∈ T, (1 : ℝ) / σ
      ≤ ((b : ℝ) - a) * R * smoothTiltBound z k t :=
    mul_le_mul_of_nonneg_left hsum hpos1
  have h2 : (T.card : ℝ) * (R + T₀) ≤ smoothIndexBound z b k * (R + T₀) :=
    mul_le_mul_of_nonneg_right hcard (by linarith)
  calc ((b : ℝ) - a) * R * ∑ σ ∈ T, (1 : ℝ) / σ + (T.card : ℝ) * (R + T₀)
      ≤ ((b : ℝ) - a) * R * smoothTiltBound z k t + smoothIndexBound z b k * (R + T₀) := by
        linarith
    _ = ((b : ℝ) - a) * R * smoothTiltBound z k t + (R + T₀) * smoothIndexBound z b k := by ring

end RHTower.Sieve
