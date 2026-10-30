import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompletedShellEnergyIsAPositiveFourierIntegral
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheDownwardPrimeRowIsAnExactLogarithmicDivisorJet
import GaloisForLFunctions.BezoutValuationIncidence.NonMarkovianLagOperatorAlgebraAndPrimePowerRevival

/-!
# The successor shells repay every conductor

Below touching the conductor-`m` complete-Weil energy is the reference energy
`E_m^ref(c) = log(1/(2πc)) + β(φ)/M + log m + τ(m) + 1_{m=1} c q`
(`completeWeilAdjunctionEnergy φ c m`). Continued past touching, every nonpolar reference energy
loses `log c` and becomes negative (`exists_overlap_all_nonpolar_reference_energies_negative`).
The successor shells `n = km + h` enter the actual form with the Ramanujan weights `c_m(h)`
of the affine prime windows. The **completed conductor energy**

`E_m(c) = φ(m)⁻¹ Σ_{d ∣ m} μ(m/d) d E(c/d)`,

built from the completed conductor-one energy `E` by Möbius inversion, satisfies:

* **Shell form** (`completedConductorEnergy_eq_reference_sub_shells`): for every `c > 0`,
  `E_m(c) = E_m^ref(c) − (2/(M φ(m))) Σ_{1≤h<c} c_m(h) ∫_{h/c}^1 G(u)/u du`;
  the Ramanujan sum `c_m(h) = Σ_{d∣(m,h)} μ(m/d) d` appears by regrouping the shells `h = h'd`.
* **Repayment** (`hasSum_completedConductorEnergy`, `completedConductorEnergy_nonneg`):
  `E_m(c) = (2/(M φ(m))) Σ_{a≥1, (a,m)=1} (m/a) ∫_{ac/m}^∞ |φ̂(2πt)|² dt ≥ 0`.
  The Möbius signs collapse to the coprimality indicator, so every shell-completed conductor
  energy is a positive Fourier integral: the shells repay the `−log c` loss exactly.
* **Marginality** (`tendsto_completedConductorEnergy_atTop`): `E_m(c) → 0`.
* **Below touching** (`completedConductorEnergy_eq_adjunction`): `E_m(c) = E_m^ref(c)` for `c ≤ 1`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset intervalIntegral
open scoped Real

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.CompletedShell

open SpacingScaleHarmonicAnalysis BezoutValuationIncidence

variable {φ : ℝ → ℝ}

/-- The **completed conductor energy** `E_m(c) = φ(m)⁻¹ Σ_{d∣m} μ(m/d) d E(c/d)`. -/
def completedConductorEnergy (φ : ℝ → ℝ) (c : ℝ) (m : ℕ) : ℝ :=
  (∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) * d * completedShellEnergy φ (c / d)) /
    m.totient

/-! ### Divisor sums -/

theorem sum_divisors_moebius_div (m : ℕ) :
    ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) = if m = 1 then 1 else 0 := by
  rw [Nat.sum_div_divisors m fun e => (ArithmeticFunction.moebius e : ℝ)]
  have h := congrArg (fun f : ArithmeticFunction ℝ => f m)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  simpa only [ArithmeticFunction.intCoe_apply] using h

theorem sum_divisors_moebius_div_mul (m : ℕ) :
    ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) * d = m.totient := by
  have h := ramanujanLagCoefficient_of_dvd (dvd_refl m)
  rw [← h, ramanujanLagCoefficient]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [if_pos (Nat.dvd_of_mem_divisors hd)]
  rfl

/-- The Möbius sum over common divisors is the coprimality indicator. -/
theorem sum_divisors_moebius_filter_dvd {m k : ℕ} (hm : 0 < m) :
    ∑ e ∈ m.divisors.filter (· ∣ k), (ArithmeticFunction.moebius e : ℝ) =
      if Nat.Coprime m k then 1 else 0 := by
  have hset : m.divisors.filter (· ∣ k) = (Nat.gcd m k).divisors := by
    ext e
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h3⟩, (Nat.gcd_pos_of_pos_left k hm).ne'⟩
    · rintro ⟨⟨h1, h3⟩, -⟩
      exact ⟨⟨h1, hm.ne'⟩, h3⟩
  rw [hset]
  have h := congrArg (fun f : ArithmeticFunction ℝ => f (Nat.gcd m k))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  simpa only [ArithmeticFunction.intCoe_apply, Nat.Coprime] using h

/-! ### The shell form -/

section ShellForm

variable (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
include hφ hsupp

omit hφ hsupp in
/-- Regrouping the shells of `E(c/d)` along multiples of `d`. -/
theorem sum_shellSum_div {c : ℝ} (hc : 0 < c) {d : ℕ} (hd : 0 < d) :
    shellSum φ (c / d) = ∑ h ∈ (Finset.Ico 1 ⌈c⌉₊).filter (d ∣ ·),
      ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  unfold shellSum
  refine Finset.sum_nbij' (fun h' => h' * d) (fun h => h / d) ?_ ?_ ?_ ?_ ?_
  · intro h' hh'
    simp only [Finset.mem_Ico, Finset.mem_filter] at hh' ⊢
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hd.ne'), ?_⟩,
      dvd_mul_left d h'⟩
    rw [Nat.lt_ceil] at hh' ⊢
    push_cast
    have := hh'.2
    rw [lt_div_iff₀ hd0] at this
    exact this
  · intro h hh
    simp only [Finset.mem_Ico, Finset.mem_filter] at hh ⊢
    obtain ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩ := hh
    rw [Nat.mul_div_cancel_left k hd]
    refine ⟨Nat.one_le_iff_ne_zero.mpr fun hk => by simp [hk] at h1, ?_⟩
    rw [Nat.lt_ceil] at h2 ⊢
    rw [lt_div_iff₀ hd0]
    push_cast at h2
    linarith
  · intro h' _
    exact Nat.mul_div_cancel h' hd
  · intro h hh
    exact Nat.div_mul_cancel (Finset.mem_filter.mp hh).2
  · intro h' _
    congr 1
    push_cast
    field_simp

variable (hM : 0 < ∫ u, φ u ^ 2)
include hM

omit hφ hsupp hM in
/-- **Shell form.** For `c > 0` and `m ≥ 1`, the completed conductor energy is the reference energy
minus the Ramanujan-weighted successor shells. -/
theorem completedConductorEnergy_eq_reference_sub_shells {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    completedConductorEnergy φ c m = completeWeilAdjunctionEnergy φ c m -
      2 / ((∫ u, φ u ^ 2) * m.totient) * ∑ h ∈ Finset.Ico 1 ⌈c⌉₊,
        ramanujanLagCoefficient m h * ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u := by
  set M := ∫ u, φ u ^ 2 with hMdef
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  -- each divisor term
  have hterm : ∀ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) * d *
      completedShellEnergy φ (c / d) =
        (ArithmeticFunction.moebius (m / d) : ℝ) * d * completeWeilSelfFinitePart φ c +
          (ArithmeticFunction.moebius (m / d) : ℝ) * d * Real.log d +
          (ArithmeticFunction.moebius (m / d) : ℝ) * completeWeilPoleShift φ c -
          2 / M * ((ArithmeticFunction.moebius (m / d) : ℝ) * d * shellSum φ (c / d)) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    unfold completedShellEnergy completeWeilSelfFinitePart completeWeilPoleShift
    rw [← hMdef]
    have hlog : Real.log (1 / (2 * π * (c / d))) = Real.log (1 / (2 * π * c)) + Real.log d := by
      rw [show 1 / (2 * π * (c / d)) = d * (1 / (2 * π * c)) by field_simp,
        Real.log_mul hd0.ne' (by positivity)]
      ring
    rw [hlog]
    field_simp
    ring
  -- the shells regroup into Ramanujan sums
  have hshell : ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) * d * shellSum φ (c / d) =
      ∑ h ∈ Finset.Ico 1 ⌈c⌉₊, ramanujanLagCoefficient m h *
        ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u := by
    have h1 : ∀ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) * d * shellSum φ (c / d) =
        ∑ h ∈ Finset.Ico 1 ⌈c⌉₊, (ArithmeticFunction.moebius (m / d) : ℝ) *
          (if d ∣ h then (d : ℝ) else 0) * ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u := by
      intro d hd
      rw [sum_shellSum_div hc (Nat.pos_of_mem_divisors hd), Finset.sum_filter,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      split_ifs <;> ring
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Finset.sum_mul, ramanujanLagCoefficient]
    rfl
  unfold completedConductorEnergy completeWeilAdjunctionEnergy ramanujanAdjunctionEnergy
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, sum_divisors_moebius_div_mul,
    CriticalArithmeticCorrelationTheory.sum_moebius_mul_divisor_log_eq_totient_excitation hm,
    sum_divisors_moebius_div, ← Finset.mul_sum, hshell]
  set I := ∑ h ∈ Finset.Ico 1 ⌈c⌉₊, ramanujanLagCoefficient m h *
    ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u with hI
  split_ifs with h1
  · subst h1
    simp only [Nat.totient_one, Nat.cast_one]
    field_simp
    ring
  · field_simp
    ring

omit hφ hsupp hM in
/-- Below touching the shell range is empty and the completed conductor energy is the reference
energy, the proved limit of the conductor-`m` Ramanujan mode for `0 < c < 1`. -/
theorem completedConductorEnergy_eq_adjunction {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) {m : ℕ}
    (hm : 0 < m) : completedConductorEnergy φ c m = completeWeilAdjunctionEnergy φ c m := by
  have hceil : ⌈c⌉₊ = 1 := by
    rw [Nat.ceil_eq_iff one_ne_zero]; norm_num; exact ⟨hc, hc1⟩
  rw [completedConductorEnergy_eq_reference_sub_shells hc hm, hceil]
  simp

/-! ### Repayment: the coprime Fourier representation -/

/-- **Repayment law.** `E_m(c) = (2/(M φ(m))) Σ_{a≥1,(a,m)=1} (m/a) ∫_{ac/m}^∞ |φ̂(2πt)|² dt`. -/
theorem hasSum_completedConductorEnergy {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    HasSum (fun n : ℕ => if Nat.Coprime m (n + 1) then
        2 / ((∫ u, φ u ^ 2) * m.totient) * ((m : ℝ) / ((n : ℝ) + 1)) *
          ∫ t in Ioi (((n : ℝ) + 1) * c / m), shellSpectrum φ t else 0)
      (completedConductorEnergy φ c m) := by
  set M := ∫ u, φ u ^ 2 with hMdef
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set T : ℝ → ℝ := fun a => ∫ t in Ioi a, shellSpectrum φ t with hT
  -- the transported series of one divisor
  set F : ℕ → ℕ → ℝ := fun d n => if (m / d) ∣ (n + 1) then
      (ArithmeticFunction.moebius (m / d) : ℝ) * (2 / (M * m.totient)) * ((m : ℝ) / ((n : ℝ) + 1)) *
        T (((n : ℝ) + 1) * c / m) else 0 with hF
  have hdiv : ∀ d ∈ m.divisors, HasSum (F d)
      ((ArithmeticFunction.moebius (m / d) : ℝ) * d * completedShellEnergy φ (c / d) / m.totient) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hdm : d * (m / d) = m := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    set e := m / d with he
    have he0 : 0 < e := Nat.div_pos (Nat.divisor_le hd) hd0
    have heR : (0 : ℝ) < e := by exact_mod_cast he0
    have hdmR : (d : ℝ) * e = m := by exact_mod_cast hdm
    set i : ℕ → ℕ := fun k => (k + 1) * e - 1 with hi
    have hi1 : ∀ k, i k + 1 = (k + 1) * e := fun k => by
      simp only [hi]; have : 1 ≤ (k + 1) * e := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    have hinj : Function.Injective i := by
      intro a b hab
      have : (a + 1) * e = (b + 1) * e := by rw [← hi1, ← hi1, hab]
      have := Nat.eq_of_mul_eq_mul_right he0 this
      omega
    have hoff : ∀ n, n ∉ Set.range i → F d n = 0 := by
      intro n hn
      simp only [hF]
      rw [if_neg]
      rintro ⟨k, hk⟩
      refine hn ⟨k - 1, ?_⟩
      have hk0 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · simp [h] at hk
        · exact h
      have : i (k - 1) + 1 = n + 1 := by rw [hi1, Nat.sub_add_cancel hk0, hk, mul_comm]
      omega
    have hbase := (hasSum_completedShellEnergy hφ hsupp hM (div_pos hc hdR)).mul_left
      ((ArithmeticFunction.moebius e : ℝ) * d / m.totient)
    have hfun : F d ∘ i = fun k : ℕ => (ArithmeticFunction.moebius e : ℝ) * d / m.totient *
        (2 / M * (((k : ℝ) + 1)⁻¹ * ∫ t in Ioi (((k : ℝ) + 1) * (c / d)), shellSpectrum φ t)) := by
      funext k
      simp only [Function.comp_apply, hF]
      rw [if_pos ⟨k + 1, by rw [hi1, mul_comm]⟩]
      have hcast : ((i k : ℕ) : ℝ) + 1 = ((k : ℝ) + 1) * e := by exact_mod_cast hi1 k
      rw [hcast]
      have harg : ((k : ℝ) + 1) * e * c / m = ((k : ℝ) + 1) * (c / d) := by
        rw [← hdmR]; field_simp
      rw [harg, ← hdmR]
      have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      field_simp
      rfl
    have hval : (ArithmeticFunction.moebius (m / d) : ℝ) * d * completedShellEnergy φ (c / d) /
        m.totient = (ArithmeticFunction.moebius e : ℝ) * d / m.totient *
          completedShellEnergy φ (c / d) := by ring
    rw [hval, ← hinj.hasSum_iff hoff, hfun]
    exact hbase
  have hpoint : ∀ n : ℕ, ∑ d ∈ m.divisors, F d n = if Nat.Coprime m (n + 1) then
      2 / (M * m.totient) * ((m : ℝ) / ((n : ℝ) + 1)) *
        ∫ t in Ioi (((n : ℝ) + 1) * c / m), shellSpectrum φ t else 0 := by
    intro n
    simp only [hF]
    rw [← Finset.sum_filter_add_sum_filter_not m.divisors (fun d => (m / d) ∣ (n + 1)),
      Finset.sum_ite_of_true (fun d hd => (Finset.mem_filter.mp hd).2),
      Finset.sum_ite_of_false (fun d hd => (Finset.mem_filter.mp hd).2), Finset.sum_const_zero,
      add_zero, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    have hreidx : ∑ d ∈ m.divisors.filter (fun d => (m / d) ∣ (n + 1)),
        (ArithmeticFunction.moebius (m / d) : ℝ) =
          ∑ e ∈ m.divisors.filter (· ∣ (n + 1)), (ArithmeticFunction.moebius e : ℝ) := by
      rw [Finset.sum_filter, Finset.sum_filter]
      exact Nat.sum_div_divisors m fun e => if e ∣ n + 1 then (ArithmeticFunction.moebius e : ℝ) else 0
    rw [hreidx, sum_divisors_moebius_filter_dvd hm]
    split_ifs <;> ring
  have hsum := hasSum_sum hdiv
  rw [← Finset.sum_div] at hsum
  have hfun : (fun n : ℕ => ∑ d ∈ m.divisors, F d n) = fun n : ℕ => if Nat.Coprime m (n + 1) then
      2 / (M * m.totient) * ((m : ℝ) / ((n : ℝ) + 1)) *
        ∫ t in Ioi (((n : ℝ) + 1) * c / m), shellSpectrum φ t else 0 := funext hpoint
  rw [hfun] at hsum
  exact hsum

/-- Every shell-completed conductor energy is nonnegative. -/
theorem completedConductorEnergy_nonneg {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    0 ≤ completedConductorEnergy φ c m := by
  refine (hasSum_completedConductorEnergy hφ hsupp hM hc hm).nonneg fun n => ?_
  split_ifs
  · refine mul_nonneg (mul_nonneg (div_nonneg zero_le_two (mul_nonneg hM.le (Nat.cast_nonneg _)))
      (div_nonneg (Nat.cast_nonneg _) (by positivity))) ?_
    exact setIntegral_nonneg measurableSet_Ioi fun t _ => shellSpectrum_nonneg t
  · exact le_rfl

/-- The completed conductor energies vanish at infinite overlap. -/
theorem tendsto_completedConductorEnergy_atTop (m : ℕ) :
    Tendsto (fun c => completedConductorEnergy φ c m) atTop (𝓝 0) := by
  have h : Tendsto (fun c => ∑ d ∈ m.divisors,
      (ArithmeticFunction.moebius (m / d) : ℝ) * d * completedShellEnergy φ (c / d)) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) * d * 0 by simp]
    refine tendsto_finsetSum _ fun d hd => ?_
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    exact ((tendsto_completedShellEnergy_atTop hφ hsupp hM).comp
      (tendsto_id.atTop_div_const hd0)).const_mul _
  simpa only [completedConductorEnergy, zero_div] using h.div_const (m.totient : ℝ)

end ShellForm

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.CompletedShell

