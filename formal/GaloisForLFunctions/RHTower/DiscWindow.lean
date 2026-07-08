import GaloisForLFunctions.RHTower.DeckWindow
import GaloisForLFunctions.RHTower.DictionarySign
import GaloisForLFunctions.Bottcher.SlitAnnulus

/-!
# The DISC bit at window level: the line-predicted deck class

The annular slit charts are translated slit annuli, hence simply connected; ξ-roots therefore
exist on them whenever the enclosed configuration accounts for all ball zeros.  On any
reflection-closed enclosed configuration the deck class value at level `2^{k+1}` equals the
line-predicted class `exp(2πi·L/2^{k+1})` (computed from on-line data alone) IF AND ONLY IF the
right-half order sum `N` is divisible by `2^k`: the discrepancy between the loop class and its
on-line prediction — the DISC bit — is exactly the window's rung datum.  The loop class alone is
blind to the split `D = L + 2N` (`deckClass_blind_to_split`); the line order sum is the second
boundary functional that, jointly with the loop class, reads the rung.
-/

namespace RHTower

open Complex Set Metric

/-! ## The annular slit charts are translated slit annuli -/

/-- The right annular slit chart is the translate of a slit annulus (slit at angle `−π`). -/
theorem chartRA_eq_image_slitAnnulus (a : ℂ) {r₀ R : ℝ} (h0 : 0 < r₀) (hrR : r₀ < R) :
    chartRA a r₀ R = (a + ·) '' Bottcher.slitAnnulus r₀ R (-Real.pi) := by
  ext z
  constructor
  · rintro ⟨hslit, hzball, hzout⟩
    have hw : z - a ∈ Complex.slitPlane := hslit
    have hnorm1 : ‖z - a‖ < R := by rwa [mem_ball, Complex.dist_eq] at hzball
    have hnorm0 : r₀ < ‖z - a‖ := by
      simp only [mem_closedBall, Complex.dist_eq, not_le] at hzout
      exact hzout
    have hargne : Complex.arg (z - a) ≠ Real.pi := by
      intro h
      rcases Complex.arg_eq_pi_iff.mp h with ⟨hre, him⟩
      rcases Complex.mem_slitPlane_iff.mp hw with h' | h'
      · linarith
      · exact h' him
    have hmem : z - a ∈ Bottcher.slitAnnulus r₀ R (-Real.pi) := by
      refine Bottcher.mem_slitAnnulus_of_arg_ne h0 ⟨hnorm0, hnorm1⟩
        ⟨Complex.arg (z - a), (Complex.arg_mem_Ioc (z - a)).1, ?_, ?_⟩
      · have hle := (Complex.arg_mem_Ioc (z - a)).2
        have h2π : -Real.pi + 2 * Real.pi = Real.pi := by ring
        rw [h2π]
        exact lt_of_le_of_ne hle hargne
      · exact (norm_mul_exp_arg_mul_I (z - a)).symm
    exact ⟨z - a, hmem, by ring⟩
  · rintro ⟨w, hw, rfl⟩
    have hann : w ∈ Bottcher.annulusSet r₀ R := Bottcher.slitAnnulus_subset h0 hrR hw
    obtain ⟨ξ, ⟨hξ1, hξ2, hξ3, hξ4⟩, rfl⟩ := hw
    have hyub : ξ.im < Real.pi := by linarith
    have heq : a + Complex.exp ξ - a = Complex.exp ξ := by ring
    refine ⟨?_, ?_, ?_⟩
    · show a + Complex.exp ξ - a ∈ Complex.slitPlane
      rw [heq]
      rcases eq_or_ne ξ.im 0 with hy | hy
      · refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
        rw [Complex.exp_re, hy, Real.cos_zero, mul_one]
        exact Real.exp_pos _
      · refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
        rw [Complex.exp_im]
        refine mul_ne_zero (Real.exp_pos _).ne' ?_
        intro hsin
        obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
        have hn0 : n = 0 := by
          by_contra hne
          have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
          have h2 : Real.pi ≤ |(n : ℝ) * Real.pi| := by
            rw [abs_mul, abs_of_pos Real.pi_pos]
            nlinarith [Real.pi_pos]
          rw [hn] at h2
          have habs : |ξ.im| < Real.pi := abs_lt.mpr ⟨hξ3, hyub⟩
          linarith
        rw [hn0] at hn
        simp only [Int.cast_zero, zero_mul] at hn
        exact hy hn.symm
    · rw [mem_ball, Complex.dist_eq, heq]
      exact hann.2
    · simp only [mem_closedBall, Complex.dist_eq, not_le, heq]
      exact hann.1

/-- The left annular slit chart is the translate of a slit annulus (slit at angle `0`). -/
theorem chartLA_eq_image_slitAnnulus (a : ℂ) {r₀ R : ℝ} (h0 : 0 < r₀) (hrR : r₀ < R) :
    chartLA a r₀ R = (a + ·) '' Bottcher.slitAnnulus r₀ R 0 := by
  ext z
  constructor
  · rintro ⟨hslit, hzball, hzout⟩
    have hw : a - z ∈ Complex.slitPlane := hslit
    have hnorm1 : ‖z - a‖ < R := by rwa [mem_ball, Complex.dist_eq] at hzball
    have hnorm0 : r₀ < ‖z - a‖ := by
      simp only [mem_closedBall, Complex.dist_eq, not_le] at hzout
      exact hzout
    have hargne : Complex.arg (z - a) ≠ 0 := by
      intro h
      rcases Complex.arg_eq_zero_iff.mp h with ⟨hre, him⟩
      rcases Complex.mem_slitPlane_iff.mp hw with h' | h'
      · rw [Complex.sub_re] at h'
        rw [Complex.sub_re] at hre
        linarith
      · rw [Complex.sub_im] at h'
        rw [Complex.sub_im] at him
        exact h' (by linarith)
    have harg_mem := Complex.arg_mem_Ioc (z - a)
    have hid := (norm_mul_exp_arg_mul_I (z - a)).symm
    have hmem : z - a ∈ Bottcher.slitAnnulus r₀ R 0 := by
      rcases lt_or_gt_of_ne hargne with hneg | hpos
      · -- arg ∈ (−π, 0): use θ = arg + 2π ∈ (π, 2π)
        refine Bottcher.mem_slitAnnulus_of_arg_ne h0 ⟨hnorm0, hnorm1⟩
          ⟨Complex.arg (z - a) + 2 * Real.pi, ?_, ?_, ?_⟩
        · have := harg_mem.1
          nlinarith [Real.pi_pos]
        · have := harg_mem.2
          nlinarith [Real.pi_pos]
        · have hexp : Complex.exp ((↑(Complex.arg (z - a) + 2 * Real.pi)) * Complex.I)
              = Complex.exp ((Complex.arg (z - a) : ℂ) * Complex.I) := by
            push_cast
            rw [add_mul, Complex.exp_add,
              show ((2 : ℂ) * (Real.pi : ℂ)) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I from
                by ring,
              Complex.exp_two_pi_mul_I, mul_one]
          rw [hexp]
          exact hid
      · -- arg ∈ (0, π]: use θ = arg
        refine Bottcher.mem_slitAnnulus_of_arg_ne h0 ⟨hnorm0, hnorm1⟩
          ⟨Complex.arg (z - a), hpos, ?_, hid⟩
        have := harg_mem.2
        nlinarith [Real.pi_pos]
    exact ⟨z - a, hmem, by ring⟩
  · rintro ⟨w, hw, rfl⟩
    have hann : w ∈ Bottcher.annulusSet r₀ R := Bottcher.slitAnnulus_subset h0 hrR hw
    obtain ⟨ξ, ⟨hξ1, hξ2, hξ3, hξ4⟩, rfl⟩ := hw
    have hylb : 0 < ξ.im := by linarith
    have hyub : ξ.im < 2 * Real.pi := by linarith
    have heq : a - (a + Complex.exp ξ) = -Complex.exp ξ := by ring
    have heq' : a + Complex.exp ξ - a = Complex.exp ξ := by ring
    refine ⟨?_, ?_, ?_⟩
    · show a - (a + Complex.exp ξ) ∈ Complex.slitPlane
      rw [heq]
      rcases eq_or_ne ξ.im Real.pi with hy | hy
      · refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
        rw [Complex.neg_re, Complex.exp_re, hy, Real.cos_pi]
        have := Real.exp_pos ξ.re
        nlinarith
      · refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
        rw [Complex.neg_im, Complex.exp_im]
        refine neg_ne_zero.mpr (mul_ne_zero (Real.exp_pos _).ne' ?_)
        intro hsin
        obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
        have hn1 : n = 1 := by
          have hpos : (0 : ℝ) < (n : ℝ) * Real.pi := hn ▸ hylb
          have hlt : (n : ℝ) * Real.pi < 2 * Real.pi := hn ▸ hyub
          have hnpos : (0 : ℝ) < (n : ℝ) := by
            by_contra hle
            push Not at hle
            nlinarith [Real.pi_pos]
          have hnlt : (n : ℝ) < 2 := by
            by_contra hge
            push Not at hge
            nlinarith [Real.pi_pos]
          have h1 : (0 : ℤ) < n := by exact_mod_cast hnpos
          have h2 : (n : ℤ) < 2 := by exact_mod_cast hnlt
          omega
        rw [hn1] at hn
        simp only [Int.cast_one, one_mul] at hn
        exact hy hn.symm
    · rw [mem_ball, Complex.dist_eq, heq']
      exact hann.2
    · simp only [mem_closedBall, Complex.dist_eq, not_le, heq']
      exact hann.1

/-- The right annular slit chart is simply connected. -/
theorem isSimplyConnected_chartRA (a : ℂ) {r₀ R : ℝ} (h0 : 0 < r₀) (hrR : r₀ < R) :
    IsSimplyConnected (chartRA a r₀ R) := by
  rw [chartRA_eq_image_slitAnnulus a h0 hrR,
    show ((a + ·) : ℂ → ℂ) = ⇑(Homeomorph.addLeft a) from rfl,
    Homeomorph.isSimplyConnected_image]
  exact Bottcher.isSimplyConnected_slitAnnulus _ h0 hrR

/-- The left annular slit chart is simply connected. -/
theorem isSimplyConnected_chartLA (a : ℂ) {r₀ R : ℝ} (h0 : 0 < r₀) (hrR : r₀ < R) :
    IsSimplyConnected (chartLA a r₀ R) := by
  rw [chartLA_eq_image_slitAnnulus a h0 hrR,
    show ((a + ·) : ℂ → ℂ) = ⇑(Homeomorph.addLeft a) from rfl,
    Homeomorph.isSimplyConnected_image]
  exact Bottcher.isSimplyConnected_slitAnnulus _ h0 hrR

end RHTower

namespace RHTower

open Complex Set Metric

/-! ## Roots exist on the annular charts of an enclosed configuration -/

/-- An enclosed factorization is nonvanishing on both annular charts: every configured zero lies
within the inner radius and the cofactor is zero-free on the ball. -/
theorem enclosed_ne_zero_on_charts {f h : ℂ → ℂ} {t : Finset ℂ} {m : ℂ → ℕ} {a : ℂ}
    {r₀ R : ℝ}
    (hρ : ∀ w ∈ t, ‖w - a‖ ≤ r₀)
    (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, f z = (∏ w ∈ t, (z - w) ^ m w) * h z) :
    (∀ z ∈ chartRA a r₀ R, f z ≠ 0) ∧ (∀ z ∈ chartLA a r₀ R, f z ≠ 0) := by
  have key : ∀ z ∈ ball a R, r₀ < ‖z - a‖ → f z ≠ 0 := by
    intro z hzball hzfar
    rw [hfact z hzball]
    refine mul_ne_zero ?_ (hh0 z hzball)
    rw [Finset.prod_ne_zero_iff]
    intro w hw
    refine pow_ne_zero _ ?_
    intro hzw
    rw [sub_eq_zero] at hzw
    rw [hzw] at hzfar
    exact absurd (hρ w hw) (not_le.mpr hzfar)
  constructor
  · rintro z ⟨-, hzball, hzout⟩
    simp only [mem_closedBall, Complex.dist_eq, not_le] at hzout
    exact key z hzball hzout
  · rintro z ⟨-, hzball, hzout⟩
    simp only [mem_closedBall, Complex.dist_eq, not_le] at hzout
    exact key z hzball hzout

/-- **Annular chart roots of an enclosed configuration exist at every level**: the charts are
simply connected and the configuration is zero-free there. -/
theorem exists_annular_roots_of_enclosed {f h : ℂ → ℂ} {t : Finset ℂ} {m : ℂ → ℕ} {a : ℂ}
    {r₀ R : ℝ} (h0 : 0 < r₀) (hrR : r₀ < R)
    (hf : AnalyticOnNhd ℂ f (ball a R))
    (hρ : ∀ w ∈ t, ‖w - a‖ ≤ r₀)
    (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, f z = (∏ w ∈ t, (z - w) ^ m w) * h z)
    {n : ℕ} (hn : 0 < n) :
    (∃ G₁, AnalyticOnNhd ℂ G₁ (chartRA a r₀ R) ∧ ∀ z ∈ chartRA a r₀ R, G₁ z ^ n = f z) ∧
      (∃ G₂, AnalyticOnNhd ℂ G₂ (chartLA a r₀ R) ∧ ∀ z ∈ chartLA a r₀ R, G₂ z ^ n = f z) := by
  obtain ⟨hneR, hneL⟩ := enclosed_ne_zero_on_charts hρ hh0 hfact
  constructor
  · obtain ⟨χ, hχan, -, hχpow⟩ := U0KummerBranch.exists_analyticOnNhd_pow_eq
      (isOpen_chartRA a r₀ R) (isSimplyConnected_chartRA a h0 hrR)
      (hf.mono fun z hz => hz.2.1) hneR hn.ne'
    exact ⟨χ, hχan, hχpow⟩
  · obtain ⟨χ, hχan, -, hχpow⟩ := U0KummerBranch.exists_analyticOnNhd_pow_eq
      (isOpen_chartLA a r₀ R) (isSimplyConnected_chartLA a h0 hrR)
      (hf.mono fun z hz => hz.2.1) hneL hn.ne'
    exact ⟨χ, hχan, hχpow⟩

/-- Enclosed factorization with the TRUE vanishing orders as exponents: iterated single-zero
peeling, each step preserving the orders at the remaining zeros. -/
theorem exists_multi_peel_orders {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (t : Finset ℂ) (htU : ∀ w ∈ t, w ∈ U)
    (hzeros : ∀ z ∈ U, f z = 0 → z ∈ t)
    (hord : ∀ w ∈ t, analyticOrderAt f w ≠ ⊤) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧ (∀ z ∈ U, h z ≠ 0) ∧
      ∀ z ∈ U, f z = (∏ w ∈ t, (z - w) ^ (analyticOrderAt f w).toNat) * h z := by
  classical
  revert f
  induction t using Finset.induction_on with
  | empty =>
    intro f hf hzeros _
    exact ⟨f, hf, fun z hz h0 => absurd (hzeros z hz h0) (Finset.notMem_empty z),
      fun z _ => by simp⟩
  | insert ρ s hρs ih =>
    intro f hf hzeros hord
    have hρU : ρ ∈ U := htU ρ (Finset.mem_insert_self ρ s)
    have hmρ : analyticOrderAt f ρ = ((analyticOrderAt f ρ).toNat : ℕ∞) :=
      (ENat.coe_toNat (hord ρ (Finset.mem_insert_self ρ s))).symm
    obtain ⟨h₁, h₁an, h₁ρ0, hfact₁, horders₁⟩ := exists_peel hU hf hρU hmρ
    have hzeros₁ : ∀ z ∈ U, h₁ z = 0 → z ∈ s := by
      intro z hz h0
      have hzρ : z ≠ ρ := fun he => h₁ρ0 (he ▸ h0)
      have hfz : f z = 0 := by rw [hfact₁ z hz, h0, mul_zero]
      rcases Finset.mem_insert.mp (hzeros z hz hfz) with he | hs
      · exact absurd he hzρ
      · exact hs
    have hordkeep : ∀ w ∈ s, analyticOrderAt h₁ w = analyticOrderAt f w := by
      intro w hw
      exact horders₁ w (htU w (Finset.mem_insert_of_mem hw)) (fun he => hρs (he ▸ hw))
    obtain ⟨h₂, h₂an, h₂0, hfact₂⟩ := ih (fun w hw => htU w (Finset.mem_insert_of_mem hw))
      h₁an hzeros₁
      (fun w hw => by rw [hordkeep w hw]; exact hord w (Finset.mem_insert_of_mem hw))
    refine ⟨h₂, h₂an, h₂0, ?_⟩
    intro z hz
    rw [Finset.prod_insert hρs]
    have hprod : ∏ w ∈ s, (z - w) ^ (analyticOrderAt h₁ w).toNat
        = ∏ w ∈ s, (z - w) ^ (analyticOrderAt f w).toNat := by
      refine Finset.prod_congr rfl ?_
      intro w hw
      rw [hordkeep w hw]
    rw [hfact₁ z hz, hfact₂ z hz, ← hprod]
    ring

/-! ## The DISC bit: loop class versus line-predicted class -/

/-- **The DISC bit reads the rung.**  For a reflection-closed enclosed configuration with
reflection-invariant multiplicities, the deck class of level-`2^{k+1}` roots equals the
line-predicted class `exp(2πi·L/2^{k+1})` — computable from on-line data alone — IFF the
right-half multiplicity sum is divisible by `2^k`.  The discrepancy between the loop class and
its on-line prediction is exactly the enclosed rung datum; the loop class alone is blind to the
split (`deckClass_blind_to_split`), so the line prediction is the second boundary functional
that, jointly with the loop, decides the rung. -/
theorem deckClass_eq_line_iff_right_dvd {k : ℕ} {t : Finset ℂ} {m : ℂ → ℕ}
    {f h G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hclosed : ∀ z ∈ t, lineReflect z ∈ t)
    (hminv : ∀ z ∈ t, m (lineReflect z) = m z)
    (hρ : ∀ z ∈ t, ‖z - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, f z = (∏ w ∈ t, (z - w) ^ m w) * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ 2 ^ (k + 1) = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ 2 ^ (k + 1) = f z) :
    (deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        = Complex.exp (2 * (Real.pi : ℂ) * I *
            ((∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z : ℕ) : ℂ)
            / ((2 ^ (k + 1) : ℕ) : ℂ)))
      ↔ 2 ^ k ∣ ∑ z ∈ t.filter (fun z => 1 / 2 < z.re), m z := by
  classical
  have hID := window_identity hclosed hminv
  have hcount := deckClass_multi_zero t (fun z => z) m h0 hrR (pow_pos two_pos (k + 1))
    hρ hh hh0 hfact hG₁ hG₂ hpG₁ hpG₂
  rw [hcount]
  have hexp_iff : ∀ x y : ℂ, (Complex.exp x = Complex.exp y ↔ Complex.exp (x - y) = 1) := by
    intro x y
    rw [Complex.exp_sub, div_eq_one_iff_eq (Complex.exp_ne_zero y)]
  rw [hexp_iff]
  have hsum : (∑ z ∈ t, ((m z : ℂ)))
      = (((∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z)
          + 2 * ∑ z ∈ t.filter (fun z => 1 / 2 < z.re), m z : ℕ) : ℂ) := by
    rw [show (∑ z ∈ t, ((m z : ℂ))) = ((∑ z ∈ t, m z : ℕ) : ℂ) from by push_cast; ring, hID]
  have harg : 2 * (Real.pi : ℂ) * I * (∑ z ∈ t, ((m z : ℂ))) / ((2 ^ (k + 1) : ℕ) : ℂ)
      - 2 * (Real.pi : ℂ) * I *
          ((∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z : ℕ) : ℂ) / ((2 ^ (k + 1) : ℕ) : ℂ)
      = 2 * (Real.pi : ℂ) * I *
          ((∑ z ∈ t.filter (fun z => 1 / 2 < z.re), m z : ℕ) : ℂ) / ((2 ^ k : ℕ) : ℂ) := by
    rw [hsum]
    have h2k1 : ((2 : ℂ)) ^ (k + 1) ≠ 0 := pow_ne_zero (k + 1) two_ne_zero
    have h2k : ((2 : ℂ)) ^ k ≠ 0 := pow_ne_zero k two_ne_zero
    push_cast [pow_succ]
    field_simp
    ring
  rw [harg, exp_two_pi_mul_div_eq_one_iff (pow_pos two_pos k)]

/-- The ξ-instance of the DISC reading: multiplicities pinned to the vanishing orders are
automatically reflection-invariant, so for any reflection-closed enclosed ξ-configuration the
deck class equals its line prediction iff the enclosed right-half order sum satisfies the rung
divisibility. -/
theorem xi_deckClass_eq_line_iff_right_dvd {k : ℕ} {t : Finset ℂ} {m : ℂ → ℕ}
    {h G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hm : ∀ z ∈ t, (m z : ℕ∞) = analyticOrderAt xi z)
    (hclosed : ∀ z ∈ t, lineReflect z ∈ t)
    (hρ : ∀ z ∈ t, ‖z - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, xi z = (∏ w ∈ t, (z - w) ^ m w) * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ 2 ^ (k + 1) = xi z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ 2 ^ (k + 1) = xi z) :
    (deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        = Complex.exp (2 * (Real.pi : ℂ) * I *
            ((∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z : ℕ) : ℂ)
            / ((2 ^ (k + 1) : ℕ) : ℂ)))
      ↔ 2 ^ k ∣ ∑ z ∈ t.filter (fun z => 1 / 2 < z.re), m z := by
  have hminv : ∀ z ∈ t, m (lineReflect z) = m z := by
    intro z hz
    have h1 : analyticOrderAt xi (lineReflect z) = analyticOrderAt xi z :=
      xi_orderAt_lineReflect z
    have h2 := hm _ (hclosed z hz)
    rw [h1, ← hm z hz] at h2
    exact Nat.cast_inj.mp h2
  exact deckClass_eq_line_iff_right_dvd h0 hrR hclosed hminv hρ hh hh0 hfact
    hG₁ hG₂ hpG₁ hpG₂

end RHTower
