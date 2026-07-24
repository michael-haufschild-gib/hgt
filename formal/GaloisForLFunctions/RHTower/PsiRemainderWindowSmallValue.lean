import GaloisForLFunctions.RHTower.PsiRemainderHarmonicSum
import GaloisForLFunctions.RHTower.LegStripThreshold

/-!
# Small remainder values in every multiplicative window

For any `δ > 0`, every window `(y, z]` with `log(z/y) > 40/δ + 2` contains
a point where `|R(m)| ≤ δm + log z + 1`:

* if `|R| < δ·id` somewhere, done;
* otherwise `R` never vanishes; if it changes sign, the crossing lemma
  yields a point with `|R| ≤ log z + 1`;
* a constant sign is impossible: the harmonic-weighted window sum would
  exceed `δ·(log(z/y) − 2) > 40`, against the uniform bound `40`.

This is the small-value supply the Erdős–Selberg contraction consumes.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- Windowed harmonic-weighted remainder bound:
`|∑_{y < n ≤ z} R(n)(1/n − 1/(n+1))| ≤ 40`. -/
theorem abs_windowed_psiRemainder_harmonic_le {y z : ℕ}
    (hy : 1 ≤ y) (hyz : y ≤ z) :
    |∑ n ∈ Finset.Ioc y z,
        psiRemainder n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))| ≤ 40 := by
  have hu : Finset.Icc 1 z = Finset.Icc 1 y ∪ Finset.Ioc y z := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 y) (Finset.Ioc y z) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_Ioc] at hx'
    omega
  have hz1 : 1 ≤ z := le_trans hy hyz
  have hJz := abs_sum_psiRemainder_harmonic_le z hz1
  have hJy := abs_sum_psiRemainder_harmonic_le y hy
  have hsum : ∑ n ∈ Finset.Icc 1 z,
      psiRemainder n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
      = (∑ n ∈ Finset.Icc 1 y,
          psiRemainder n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)))
        + ∑ n ∈ Finset.Ioc y z,
            psiRemainder n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
    rw [hu, Finset.sum_union hdisj]
  have habs := abs_le.1 hJz
  have habs' := abs_le.1 hJy
  rw [hsum] at habs
  rw [abs_le]
  constructor <;> linarith [habs.1, habs.2, habs'.1, habs'.2]

/-- Harmonic lower bound on a window:
`∑_{y < n ≤ z} 1/(n+1) ≥ log z − log y − 2`. -/
theorem sum_inv_succ_window_ge {y z : ℕ} (hy : 1 ≤ y) (hyz : y ≤ z) :
    Real.log z - Real.log y - 2
      ≤ ∑ n ∈ Finset.Ioc y z, 1 / ((n : ℝ) + 1) := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  -- reindex to the corpus harmonic tail bound at offset `y + 2`
  have hre : ∑ j ∈ Finset.range (z - y), 1 / (((y + 2 : ℕ) : ℝ) + j)
      = ∑ n ∈ Finset.Ioc y z, 1 / ((n : ℝ) + 1) := by
    apply Finset.sum_nbij' (i := fun j => y + 1 + j) (j := fun n => n - (y + 1))
    · intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.mem_Ioc]
      omega
    · intro n hn
      rw [Finset.mem_Ioc] at hn
      rw [Finset.mem_range]
      omega
    · intro j _
      omega
    · intro n hn
      rw [Finset.mem_Ioc] at hn
      omega
    · intro j _
      push_cast
      ring_nf
  have hcorpus := harmonic_log_upper (y + 2) (by omega) (z - y)
  rw [hre] at hcorpus
  have hval : (((y + 2 : ℕ) : ℝ) + ((z - y : ℕ) : ℝ)) / ((y + 2 : ℕ) : ℝ)
      = ((z : ℝ) + 2) / ((y : ℝ) + 2) := by
    have hc : ((z - y : ℕ) : ℝ) = (z : ℝ) - y := by
      rw [Nat.cast_sub hyz]
    rw [hc]
    push_cast
    ring_nf
  rw [hval, Real.log_div (by positivity) (by positivity)] at hcorpus
  -- `log z − log y − 2 ≤ log(z+2) − log(y+2)`
  have h1 : Real.log z ≤ Real.log ((z : ℝ) + 2) := by
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < z))
    linarith
  have h2 : Real.log ((y : ℝ) + 1) ≤ Real.log y + 1 := by
    have := log_succ_sub_log_le hy
    have h3 : (1 : ℝ) / y ≤ 1 := by
      rw [div_le_one hy0]
      exact_mod_cast hy
    linarith
  have h4 : Real.log ((y : ℝ) + 2) ≤ Real.log ((y : ℝ) + 1) + 1 := by
    have h5 := log_succ_sub_log_le (j := y + 1) (by omega)
    have hc : ((y + 1 : ℕ) : ℝ) = (y : ℝ) + 1 := by push_cast; ring
    rw [hc] at h5
    have h6 : (1 : ℝ) / ((y : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h7 : (y : ℝ) + 1 + 1 = (y : ℝ) + 2 := by ring
    rw [h7] at h5
    linarith
  linarith

/-- **Small remainder in every wide window**: if `log(z/y) > 40/δ + 2`
then some `m ∈ (y, z]` has `|R(m)| ≤ δm + log z + 1`. -/
theorem exists_small_psiRemainder_in_window {y z : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hy : 1 ≤ y) (hyz : y ≤ z)
    (hbig : 40 / δ + 2 < Real.log z - Real.log y) :
    ∃ m ∈ Finset.Ioc y z, |psiRemainder m| ≤ δ * m + Real.log z + 1 := by
  have hz1 : 1 ≤ z := le_trans hy hyz
  have hlz0 : 0 ≤ Real.log z := Real.log_nonneg (by exact_mod_cast hz1)
  have hyz' : y < z := by
    by_contra hcon
    have hzy : z ≤ y := by omega
    have : Real.log z ≤ Real.log y :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < z))
        (by exact_mod_cast hzy)
    have hpos : 0 < 40 / δ + 2 := by positivity
    linarith
  by_cases hA : ∃ n ∈ Finset.Ioc y z, |psiRemainder n| < δ * n
  · obtain ⟨n, hn, hlt⟩ := hA
    exact ⟨n, hn, by linarith⟩
  · simp only [not_exists, not_and, not_lt] at hA
    by_cases hsgn : ∃ a ∈ Finset.Ioc y z, ∃ b ∈ Finset.Ioc y z,
        psiRemainder a * psiRemainder b ≤ 0
    · obtain ⟨a, ha, b, hb, hab⟩ := hsgn
      rw [Finset.mem_Ioc] at ha hb
      rcases le_total a b with hle | hle
      · obtain ⟨m, hm, hbound⟩ :=
          exists_abs_psiRemainder_le_of_sign_change
            (by omega : 1 ≤ a) hle hab
        rw [Finset.mem_Icc] at hm
        refine ⟨m, Finset.mem_Ioc.2 ⟨by omega, by omega⟩, ?_⟩
        have hlogm : Real.log b ≤ Real.log z :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < b))
            (by exact_mod_cast hb.2)
        have hδm : 0 ≤ δ * m := by positivity
        linarith
      · have hab' : psiRemainder b * psiRemainder a ≤ 0 := by
          rw [mul_comm]
          exact hab
        obtain ⟨m, hm, hbound⟩ :=
          exists_abs_psiRemainder_le_of_sign_change
            (by omega : 1 ≤ b) hle hab'
        rw [Finset.mem_Icc] at hm
        refine ⟨m, Finset.mem_Ioc.2 ⟨by omega, by omega⟩, ?_⟩
        have hlogm : Real.log a ≤ Real.log z :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < a))
            (by exact_mod_cast ha.2)
        have hδm : 0 ≤ δ * m := by positivity
        linarith
    · -- constant strict sign: contradiction with the window bound
      exfalso
      simp only [not_exists, not_and, not_le] at hsgn
      have hn₀ : y + 1 ∈ Finset.Ioc y z := Finset.mem_Ioc.2 ⟨by omega, by omega⟩
      have hW := abs_le.1 (abs_windowed_psiRemainder_harmonic_le hy hyz)
      have hwpos : ∀ n ∈ Finset.Ioc y z,
          (0 : ℝ) ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
        intro n hn
        rw [Finset.mem_Ioc] at hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        rw [sub_nonneg]
        apply div_le_div_of_nonneg_left one_pos.le hn0
        linarith
      have hnw : ∀ n ∈ Finset.Ioc y z,
          δ * (1 / ((n : ℝ) + 1))
            = δ * ((n : ℝ) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) := by
        intro n hn
        rw [Finset.mem_Ioc] at hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        congr 1
        field_simp
        ring
      have hharm := sum_inv_succ_window_ge hy hyz
      have hvalpos : ∑ n ∈ Finset.Ioc y z,
          (δ * n) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
          = δ * ∑ n ∈ Finset.Ioc y z, 1 / ((n : ℝ) + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [hnw n hn]
        ring
      have hlarge : 40 < δ * ∑ n ∈ Finset.Ioc y z, 1 / ((n : ℝ) + 1) := by
        have h1 : 40 / δ < Real.log z - Real.log y - 2 := by linarith
        have h2 : 40 / δ * δ < (Real.log z - Real.log y - 2) * δ :=
          mul_lt_mul_of_pos_right h1 hδ
        rw [div_mul_cancel₀ _ hδ.ne'] at h2
        have h3 : (Real.log z - Real.log y - 2) * δ
            ≤ (∑ n ∈ Finset.Ioc y z, 1 / ((n : ℝ) + 1)) * δ :=
          mul_le_mul_of_nonneg_right hharm hδ.le
        nlinarith [h2, h3]
      rcases lt_trichotomy (psiRemainder (y + 1)) 0 with hneg | hzero | hpos
      · -- all negative: the window sum is ≤ −δ·(harmonic window)
        have hallneg : ∀ n ∈ Finset.Ioc y z, psiRemainder n ≤ -(δ * n) := by
          intro n hn
          have hprod := hsgn (y + 1) hn₀ n hn
          have hRn : psiRemainder n < 0 := by
            by_contra hge
            rw [not_lt] at hge
            nlinarith [hprod]
          have := hA n hn
          rw [abs_of_neg hRn] at this
          linarith
        have hsum : ∑ n ∈ Finset.Ioc y z,
            psiRemainder n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
            ≤ ∑ n ∈ Finset.Ioc y z,
                -(δ * n) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
          apply Finset.sum_le_sum
          intro n hn
          exact mul_le_mul_of_nonneg_right (hallneg n hn) (hwpos n hn)
        have hval : ∑ n ∈ Finset.Ioc y z,
            -(δ * n) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
            = -(δ * ∑ n ∈ Finset.Ioc y z, 1 / ((n : ℝ) + 1)) := by
          have h1 : ∀ n ∈ Finset.Ioc y z,
              -(δ * n) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
                = -((δ * n) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) := by
            intro n _
            ring
          rw [Finset.sum_congr rfl h1, Finset.sum_neg_distrib, hvalpos]
        rw [hval] at hsum
        linarith [hW.1]
      · have := hA (y + 1) hn₀
        rw [hzero, abs_zero] at this
        have : (0 : ℝ) < δ * (y + 1 : ℕ) := by positivity
        linarith
      · -- all positive: the window sum is ≥ δ·(harmonic window)
        have hallpos : ∀ n ∈ Finset.Ioc y z, δ * n ≤ psiRemainder n := by
          intro n hn
          have hprod := hsgn (y + 1) hn₀ n hn
          have hRn : 0 < psiRemainder n := by
            by_contra hge
            rw [not_lt] at hge
            nlinarith [hprod]
          have := hA n hn
          rw [abs_of_pos hRn] at this
          linarith
        have hsum : ∑ n ∈ Finset.Ioc y z,
            (δ * n) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
            ≤ ∑ n ∈ Finset.Ioc y z,
                psiRemainder n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
          apply Finset.sum_le_sum
          intro n hn
          exact mul_le_mul_of_nonneg_right (hallpos n hn) (hwpos n hn)
        rw [hvalpos] at hsum
        linarith [hW.2]

end RHTower
