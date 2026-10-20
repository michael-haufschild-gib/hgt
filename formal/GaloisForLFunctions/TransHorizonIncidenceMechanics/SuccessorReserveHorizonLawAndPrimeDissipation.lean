import GaloisForLFunctions.TransHorizonIncidenceMechanics.BuchstabSlopeInheritanceAndSelbergDerivative
import GaloisForLFunctions.BezoutValuationIncidence.PrimeTailCalibrationAndMobiusDefect

/-!
# The horizon law of the dissipation rate

The successor reserve `R_N(c) = Q_Sel(N,c) - Q_Bez(N,c)` is the rate at which the renormalized
defect dissipates over a full period. Since `1/lcm(d,e) = gcd(d,e)/(de)`, the coprime pairs of the
Selberg kernel are exactly the Bézout kernel, so

`R_N(c) = Σ_{d,e ≤ N, gcd(d,e) > 1} c(d) c(e) gcd(d,e)/(de)`:

the dissipation rate is the non-coprime part of the lcm kernel. Across a horizon step `m ≥ 2`,

`R_m - R_{m-1} = (c(m)² + 2 c(m) Σ_{d<m, gcd(d,m)>1} c(d) gcd(d,m)/d)/m`.

* **Prime horizons.** No `d < p` shares a factor with a prime `p`, so for every weight
  `R_p - R_{p-1} = c(p)²/p`: the dissipation rate never decreases at a prime horizon, and the
  Möbius cancellation that governs the Selberg and Bézout steps separately drops out of their
  difference.
* **Prime-supported weights** (`c` vanishing on composite integers) dissipate at the exact rate
  `R_N(c) = Σ_{p ≤ N} c(p)²/p`.
* **Möbius.** `R_m - R_{m-1} = μ(m)² ϑ(m)/m` with the reserve slope
  `ϑ(m) = 1 + 2μ(m) Σ_{d<m, gcd(d,m)>1} μ(d) gcd(d,m)/d = λ(m) - 2μ(m) m_m(m-1)`: `ϑ(p) = 1`, and
  for squarefree `a` the slope of `aq` tends to the Buchstab slope `λ(a)` as the prime `q` grows.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The non-coprime part of the lcm kernel: `gcd(d,e)/(de)` if `gcd(d,e) > 1`, else `0`. -/
def nonCoprimeLcmKernel (d e : ℕ) : ℝ :=
  if Nat.Coprime d e then 0 else ((Nat.gcd d e : ℕ) : ℝ) / ((d : ℝ) * e)

private theorem inv_lcm_eq_gcd_div {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    (1 : ℝ) / (Nat.lcm d e : ℝ) = ((Nat.gcd d e : ℕ) : ℝ) / ((d : ℝ) * e) := by
  have hgl : ((Nat.gcd d e : ℕ) : ℝ) * (Nat.lcm d e : ℝ) = (d : ℝ) * e := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  have hl : (0 : ℝ) < (Nat.lcm d e : ℝ) := by exact_mod_cast Nat.lcm_pos hd he
  rw [div_eq_div_iff hl.ne' (by positivity)]
  linarith

/-- **Kernel form.** `R_N(c) = Σ_{d,e ≤ N} c(d) c(e) K(d,e)` with the non-coprime lcm kernel. -/
theorem sieveSuccessorReserve_eq_sum_nonCoprimeLcmKernel (N : ℕ) (c : ℕ → ℝ) :
    sieveSuccessorReserve N c =
      ∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N), c p.1 * c p.2 * nonCoprimeLcmKernel p.1 p.2 := by
  unfold sieveSuccessorReserve
  rw [← sum_div_lcm_eq_selbergTotientDiagonalForm, bezoutCoprimeQuadraticForm, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  obtain ⟨h1, h2⟩ := mem_product.mp hp
  have hd : 0 < p.1 := (mem_Icc.mp h1).1
  have he : 0 < p.2 := (mem_Icc.mp h2).1
  have hinv := inv_lcm_eq_gcd_div hd he
  unfold nonCoprimeLcmKernel
  by_cases hc : Nat.Coprime p.1 p.2
  · rw [if_pos hc, if_pos hc]
    have hg : ((Nat.gcd p.1 p.2 : ℕ) : ℝ) = 1 := by rw [hc.gcd_eq_one, Nat.cast_one]
    rw [hg] at hinv
    have hd' : (0 : ℝ) < p.1 := by exact_mod_cast hd
    have he' : (0 : ℝ) < p.2 := by exact_mod_cast he
    calc c p.1 * c p.2 / (Nat.lcm p.1 p.2 : ℝ) - 1 * (c p.1 / p.1) * (c p.2 / p.2)
        = c p.1 * c p.2 * ((1 : ℝ) / (Nat.lcm p.1 p.2 : ℝ)) -
            c p.1 * c p.2 * (1 / ((p.1 : ℝ) * p.2)) := by field_simp
      _ = 0 := by rw [hinv]; ring
      _ = c p.1 * c p.2 * 0 := by ring
  · rw [if_neg hc, if_neg hc]
    calc c p.1 * c p.2 / (Nat.lcm p.1 p.2 : ℝ) - 0 * (c p.1 / p.1) * (c p.2 / p.2)
        = c p.1 * c p.2 * ((1 : ℝ) / (Nat.lcm p.1 p.2 : ℝ)) := by ring
      _ = _ := by rw [hinv]

private theorem product_form_split (N : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ p ∈ (Icc 1 (N + 1)) ×ˢ (Icc 1 (N + 1)), f p.1 p.2) =
      (∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N), f p.1 p.2) + (∑ d ∈ Icc 1 N, f d (N + 1)) +
        (∑ e ∈ Icc 1 N, f (N + 1) e) + f (N + 1) (N + 1) := by
  rw [sum_product, sum_product, sum_Icc_succ_top (by omega)]
  simp_rw [sum_Icc_succ_top (show 1 ≤ N + 1 by omega)]
  rw [sum_add_distrib]
  ring

/-- **Horizon law of the dissipation rate.** For every weight and every horizon `m = n + 1 ≥ 2`,
`R_m - R_{m-1} = (c(m)² + 2c(m) Σ_{d<m, gcd(d,m)>1} c(d) gcd(d,m)/d)/m`. -/
theorem sieveSuccessorReserve_succ_sub {n : ℕ} (hn : 1 ≤ n) (c : ℕ → ℝ) :
    sieveSuccessorReserve (n + 1) c - sieveSuccessorReserve n c =
      (c (n + 1) ^ 2 + 2 * c (n + 1) * ∑ d ∈ Icc 1 n,
        (if Nat.Coprime d (n + 1) then 0 else c d * ((Nat.gcd d (n + 1) : ℕ) : ℝ) / (d : ℝ))) /
        ((n : ℝ) + 1) := by
  rw [sieveSuccessorReserve_eq_sum_nonCoprimeLcmKernel,
    sieveSuccessorReserve_eq_sum_nonCoprimeLcmKernel,
    product_form_split n (fun d e => c d * c e * nonCoprimeLcmKernel d e)]
  have hsym : (∑ e ∈ Icc 1 n, c (n + 1) * c e * nonCoprimeLcmKernel (n + 1) e) =
      ∑ d ∈ Icc 1 n, c d * c (n + 1) * nonCoprimeLcmKernel d (n + 1) := by
    refine sum_congr rfl fun e _ => ?_
    unfold nonCoprimeLcmKernel
    by_cases h : Nat.Coprime e (n + 1)
    · rw [if_pos h.symm, if_pos h]; ring
    · rw [if_neg (fun h' => h h'.symm), if_neg h, Nat.gcd_comm]; ring
  have hdiag : nonCoprimeLcmKernel (n + 1) (n + 1) = 1 / ((n : ℝ) + 1) := by
    unfold nonCoprimeLcmKernel
    rw [if_neg (by rw [Nat.coprime_self]; omega), Nat.gcd_self]
    push_cast
    field_simp
  have hcross : ∀ d ∈ Icc 1 n, c d * c (n + 1) * nonCoprimeLcmKernel d (n + 1) =
      c (n + 1) * (if Nat.Coprime d (n + 1) then 0 else
        c d * ((Nat.gcd d (n + 1) : ℕ) : ℝ) / (d : ℝ)) / ((n : ℝ) + 1) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    unfold nonCoprimeLcmKernel
    split_ifs
    · ring
    · push_cast; field_simp
  rw [hsym, sum_congr rfl hcross, hdiag, ← sum_div, ← mul_sum]
  field_simp
  ring

/-- **Prime horizons.** For every weight and prime `p`, `R_p - R_{p-1} = c(p)²/p`. -/
theorem sieveSuccessorReserve_prime_step {p : ℕ} (hp : p.Prime) (c : ℕ → ℝ) :
    sieveSuccessorReserve p c - sieveSuccessorReserve (p - 1) c = c p ^ 2 / p := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.one_le; omega⟩
  have hn : 1 ≤ n := by have := hp.two_le; omega
  rw [show n + 1 - 1 = n by omega, sieveSuccessorReserve_succ_sub hn c]
  have hzero : (∑ d ∈ Icc 1 n,
      (if Nat.Coprime d (n + 1) then 0 else c d * ((Nat.gcd d (n + 1) : ℕ) : ℝ) / (d : ℝ))) = 0 := by
    refine sum_eq_zero fun d hd => ?_
    have hcop : Nat.Coprime d (n + 1) := ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => by
      have := Nat.le_of_dvd (mem_Icc.mp hd).1 h; have := (mem_Icc.mp hd).2; omega).symm
    rw [if_pos hcop]
  rw [hzero]
  push_cast
  ring

/-- The dissipation rate never decreases at a prime horizon. -/
theorem sieveSuccessorReserve_prime_mono {p : ℕ} (hp : p.Prime) (c : ℕ → ℝ) :
    sieveSuccessorReserve (p - 1) c ≤ sieveSuccessorReserve p c := by
  have h := sieveSuccessorReserve_prime_step hp c
  have : 0 ≤ c p ^ 2 / p := by positivity
  linarith

/-- **Prime-supported weights.** If `c` vanishes on composite integers, then
`R_N(c) = Σ_{p ≤ N prime} c(p)²/p`. -/
theorem sieveSuccessorReserve_of_prime_support {c : ℕ → ℝ}
    (hc : ∀ d, 2 ≤ d → ¬ d.Prime → c d = 0) (N : ℕ) :
    sieveSuccessorReserve N c = ∑ p ∈ (Icc 1 N).filter Nat.Prime, c p ^ 2 / p := by
  rw [sieveSuccessorReserve_eq_sum_nonCoprimeLcmKernel, sum_product, sum_filter]
  refine sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
  -- only the diagonal survives, and only at primes
  have hoff : ∀ e ∈ Icc 1 N, e ≠ d → c d * c e * nonCoprimeLcmKernel d e = 0 := by
    intro e he hne
    have he1 : 1 ≤ e := (mem_Icc.mp he).1
    by_cases hcd : c d = 0
    · rw [hcd]; ring
    by_cases hce : c e = 0
    · rw [hce]; ring
    have hcop : Nat.Coprime d e := by
      rcases (show d = 1 ∨ 2 ≤ d by omega) with rfl | hd2
      · exact Nat.coprime_one_left e
      rcases (show e = 1 ∨ 2 ≤ e by omega) with rfl | he2
      · exact Nat.coprime_one_right d
      have hdp : d.Prime := by by_contra h; exact hcd (hc d hd2 h)
      have hep : e.Prime := by by_contra h; exact hce (hc e he2 h)
      exact (Nat.coprime_primes hdp hep).mpr hne.symm
    unfold nonCoprimeLcmKernel; rw [if_pos hcop]; ring
  rw [sum_eq_single_of_mem d hd hoff]
  unfold nonCoprimeLcmKernel
  by_cases hp : d.Prime
  · rw [if_pos hp, if_neg (by rw [Nat.coprime_self]; exact hp.one_lt.ne'), Nat.gcd_self]
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hp.pos
    field_simp
  · rw [if_neg hp]
    rcases (show d = 1 ∨ 2 ≤ d by omega) with rfl | hd2
    · rw [if_pos (Nat.coprime_one_left 1)]; ring
    · rw [hc d hd2 hp]; ring

/-! ### Möbius reserve slopes -/

/-- The **reserve slope** `ϑ(m) = 1 + 2μ(m) Σ_{d<m, gcd(d,m)>1} μ(d) gcd(d,m)/d`. -/
def reserveSlope (m : ℕ) : ℝ :=
  1 + 2 * moebiusReal m * ∑ d ∈ Icc 1 (m - 1),
    (if Nat.Coprime d m then 0 else moebiusReal d * ((Nat.gcd d m : ℕ) : ℝ) / (d : ℝ))

/-- The Möbius dissipation rate moves by `μ(m)² ϑ(m)/m` at the horizon `m ≥ 2`. -/
theorem sieveSuccessorReserve_moebius_step {n : ℕ} (hn : 1 ≤ n) :
    sieveSuccessorReserve (n + 1) moebiusReal - sieveSuccessorReserve n moebiusReal =
      moebiusReal (n + 1) ^ 2 * reserveSlope (n + 1) / ((n : ℝ) + 1) := by
  rw [sieveSuccessorReserve_succ_sub hn, reserveSlope, show n + 1 - 1 = n by omega]
  have hμ3 : moebiusReal (n + 1) ^ 2 * moebiusReal (n + 1) = moebiusReal (n + 1) := by
    unfold moebiusReal
    rcases eq_or_ne (μ (n + 1)) 0 with h | h
    · simp [h]
    · have hsq : Squarefree (n + 1) := by
        by_contra hs; exact h (moebius_eq_zero_of_not_squarefree hs)
      have h1 : |(μ (n + 1) : ℝ)| = 1 := by exact_mod_cast abs_moebius_eq_one_of_squarefree hsq
      have h2 : (μ (n + 1) : ℝ) ^ 2 = 1 := by rw [← sq_abs, h1, one_pow]
      rw [h2, one_mul]
  set S := ∑ d ∈ Icc 1 n, (if Nat.Coprime d (n + 1) then 0 else
    moebiusReal d * ((Nat.gcd d (n + 1) : ℕ) : ℝ) / (d : ℝ))
  have key : moebiusReal (n + 1) ^ 2 + 2 * moebiusReal (n + 1) * S =
      moebiusReal (n + 1) ^ 2 * (1 + 2 * moebiusReal (n + 1) * S) := by
    linear_combination (-2 * S) * hμ3
  rw [key]

/-- `ϑ(m) = λ(m) - 2μ(m) m_m(m-1)`: the reserve slope is the Buchstab slope minus the coprime
harmonic Möbius sum. -/
theorem reserveSlope_eq_buchstabSlope_sub (m : ℕ) :
    reserveSlope m = buchstabSlope m - 2 * moebiusReal m * coprimeHarmonicMoebius m (m - 1) := by
  rw [reserveSlope, buchstabSlope_eq_core, buchstabSlopeCore, coprimeHarmonicMoebius]
  have h : (∑ d ∈ Icc 1 (m - 1), moebiusReal d * ((Nat.gcd d m : ℕ) : ℝ) / (d : ℝ)) =
      (∑ d ∈ Icc 1 (m - 1), if Nat.Coprime d m then moebiusReal d / (d : ℝ) else 0) +
      ∑ d ∈ Icc 1 (m - 1), (if Nat.Coprime d m then 0 else
        moebiusReal d * ((Nat.gcd d m : ℕ) : ℝ) / (d : ℝ)) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun d _ => ?_
    split_ifs with hc
    · rw [hc.gcd_eq_one]; push_cast; ring
    · ring
  rw [h]
  ring

/-- At a prime horizon the reserve slope is exactly one. -/
theorem reserveSlope_prime {p : ℕ} (hp : p.Prime) : reserveSlope p = 1 := by
  rw [reserveSlope]
  have hzero : (∑ d ∈ Icc 1 (p - 1), (if Nat.Coprime d p then 0 else
      moebiusReal d * ((Nat.gcd d p : ℕ) : ℝ) / (d : ℝ))) = 0 := by
    refine sum_eq_zero fun d hd => ?_
    have hcop : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => by
      have := Nat.le_of_dvd (mem_Icc.mp hd).1 h; have := (mem_Icc.mp hd).2
      have := hp.one_le; omega).symm
    rw [if_pos hcop]
  rw [hzero]; ring

/-- Attaching a large prime: `m_{aq}(aq - 1) = m_a(aq - 1) + m_a(a - 1)/q` for a prime `q > a`. -/
theorem coprimeHarmonicMoebius_mul_prime {a q : ℕ} (ha : 1 ≤ a) (hq : q.Prime) (haq : a < q) :
    coprimeHarmonicMoebius (a * q) (a * q - 1) =
      coprimeHarmonicMoebius a (a * q - 1) + coprimeHarmonicMoebius a (a - 1) / q := by
  have hqa : ¬ q ∣ a := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hstep := coprimeHarmonicMoebius_prime_step hq hqa (a * q - 1)
  have hdiv : (a * q - 1) / q = a - 1 := by
    apply Nat.div_eq_of_lt_le
    · have : (a - 1) * q + q = a * q := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel ha]
      omega
    · rw [Nat.sub_add_cancel ha]
      have : 0 < a * q := Nat.mul_pos (by omega) hq.pos
      omega
  have hlow : coprimeHarmonicMoebius (a * q) (a - 1) = coprimeHarmonicMoebius a (a - 1) := by
    unfold coprimeHarmonicMoebius
    refine sum_congr rfl fun d hd => ?_
    have hdq : Nat.Coprime d q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr fun h => by
      have := Nat.le_of_dvd (mem_Icc.mp hd).1 h; have := (mem_Icc.mp hd).2; omega).symm
    simp only [Nat.coprime_mul_iff_right]
    by_cases hda : Nat.Coprime d a
    · rw [if_pos ⟨hda, hdq⟩, if_pos hda]
    · rw [if_neg (fun h => hda h.1), if_neg hda]
  rw [hdiv, hlow] at hstep
  linarith

/-- **Reserve-slope inheritance.** For squarefree `a`, the reserve slope of `aq` tends to the
Buchstab slope `λ(a)` as the prime `q` grows. -/
theorem tendsto_reserveSlope_mul_prime {a : ℕ} (ha : Squarefree a) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, q.Prime → |reserveSlope (a * q) - buchstabSlope a| < ε := by
  have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha.ne_zero
  have hm : Tendsto (coprimeHarmonicMoebius a) atTop (𝓝 0) := by
    have h := tendsto_coprimeHarmonicMoebius_prod a.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
    rwa [Nat.prod_primeFactors_of_squarefree ha] at h
  have hshift : Tendsto (fun q : ℕ => a * q - 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b + 1, fun q hq => by
      have : q ≤ a * q := Nat.le_mul_of_pos_left q (by omega)
      omega⟩
  have hmq := (hm.comp hshift).eventually (Metric.ball_mem_nhds (0 : ℝ) (by positivity :
    (0 : ℝ) < ε / 8))
  have hconst : ∀ᶠ q : ℕ in atTop, |coprimeHarmonicMoebius a (a - 1)| / (q : ℝ) < ε / 8 := by
    have h := (tendsto_const_nhds (x := |coprimeHarmonicMoebius a (a - 1)|)).div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
    exact h.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [tendsto_buchstabSlope_mul_prime ha (ε / 2) (by positivity), hmq, hconst,
    eventually_gt_atTop a] with q hlam hmq' hc haq hq
  simp only [Function.comp, Real.dist_eq, sub_zero] at hmq'
  have hlamq := hlam hq
  rw [reserveSlope_eq_buchstabSlope_sub, coprimeHarmonicMoebius_mul_prime ha1 hq haq]
  have hμ : |moebiusReal (a * q)| ≤ 1 := by
    unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hsmall : |coprimeHarmonicMoebius a (a * q - 1) + coprimeHarmonicMoebius a (a - 1) / q| <
      ε / 4 := by
    calc _ ≤ |coprimeHarmonicMoebius a (a * q - 1)| + |coprimeHarmonicMoebius a (a - 1) / q| :=
          abs_add_le _ _
      _ < ε / 8 + ε / 8 := by rw [abs_div, abs_of_pos hq0]; linarith
      _ = ε / 4 := by ring
  have hprod : |2 * moebiusReal (a * q) *
      (coprimeHarmonicMoebius a (a * q - 1) + coprimeHarmonicMoebius a (a - 1) / q)| ≤ ε / 2 := by
    rw [abs_mul, abs_mul, abs_two]
    nlinarith [abs_nonneg (moebiusReal (a * q)), abs_nonneg
      (coprimeHarmonicMoebius a (a * q - 1) + coprimeHarmonicMoebius a (a - 1) / q)]
  calc |buchstabSlope (a * q) - 2 * moebiusReal (a * q) *
        (coprimeHarmonicMoebius a (a * q - 1) + coprimeHarmonicMoebius a (a - 1) / q) -
        buchstabSlope a|
      ≤ |buchstabSlope (a * q) - buchstabSlope a| + |2 * moebiusReal (a * q) *
        (coprimeHarmonicMoebius a (a * q - 1) + coprimeHarmonicMoebius a (a - 1) / q)| := by
        rw [show buchstabSlope (a * q) - 2 * moebiusReal (a * q) *
          (coprimeHarmonicMoebius a (a * q - 1) + coprimeHarmonicMoebius a (a - 1) / q) -
          buchstabSlope a = (buchstabSlope (a * q) - buchstabSlope a) - 2 * moebiusReal (a * q) *
          (coprimeHarmonicMoebius a (a * q - 1) + coprimeHarmonicMoebius a (a - 1) / q) by ring]
        exact abs_sub _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
