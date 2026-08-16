import GaloisForLFunctions.RHTower.XiMassAnnulusPhaseProjection

/-!
# Theorem 17.5: the subthreshold raw-annulus lower bound

Between two cone slopes `1 < κ < λ` the moving prime annulus is bounded below by

`‖A_{κ,λ}(u)‖ ≥ c · u^{-1/2} e^{γ u}`,  `γ = κ/2 − a√(κ²−1)`,

for all large heights.  Three facts combine.

* The shell asymptotic (17.20) makes every atom with `κu < log p ≤ κu+L` point, to relative
  accuracy `1/u`, along one fixed unit phase, so their real parts *add*.
* The prime number theorem (17.21) gives the innermost unit shell a mass at least
  `½(e−1)e^{κu}`.
* The exterior tail (17.23) past `e^{κu+L}` is smaller than `C e^{-(a-1/2)L} u^{-1/2}e^{γu}`, so a
  fixed large `L` makes it a small fraction of the shell.

Below the Bessel balance slope `γ` is positive, so the annulus diverges: the closed cone of
Theorem 17.3 cannot be shrunk.
-/

open Complex Filter Finset MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- The phase-projected atom in the shell is bounded below by its modulus. -/
theorem re_conj_phase_atom_ge {a sigma kappa u s CR : ℝ} {p : ℕ} (hkappa : 1 < kappa) (hu : 0 < u)
    (hp : p.Prime) (hlog : Real.log p = kappa * u + s)
    (hbound : ‖xiMassCriticalDampedFourierProfile a sigma u (kappa * u + s)
        - shellLeadingDamped a sigma kappa u s‖ ≤ CR / u * shellModulus a kappa u s) :
    Real.log p * ((1 - CR / u) * shellModulus a kappa u s)
      ≤ ((starRingEnd ℂ) (shellPhase a sigma kappa)
          * xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) p).re := by
  have hlogpos : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hatom : (starRingEnd ℂ) (shellPhase a sigma kappa)
      * xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) p
      = ((Real.log p : ℝ) : ℂ) * ((starRingEnd ℂ) (shellPhase a sigma kappa)
        * xiMassCriticalDampedFourierProfile a sigma u (kappa * u + s)) := by
    rw [xiMassCenteredPrimeAtom_eq_log_mul hp, hlog]
    ring
  rw [hatom, Complex.re_ofReal_mul]
  exact mul_le_mul_of_nonneg_left (re_conj_shellPhase_mul_profile_ge hkappa hu hbound) hlogpos

/-- Inside the window `κu < log p ≤ κu + t ≤ κu + L` the phase-projected atom is at least half
the shell modulus at the outer edge times `log p`. -/
theorem re_conj_phase_atom_window {a sigma kappa u CR L t : ℝ} {k : ℕ}
    (ha : 0 < a) (hkappa : 1 < kappa) (hu : 0 < u) (hCR : CR / u ≤ 1 / 2)
    (hrel : ∀ s : ℝ, 0 ≤ s → s ≤ L →
      ‖xiMassCriticalDampedFourierProfile a sigma u (kappa * u + s)
        - shellLeadingDamped a sigma kappa u s‖ ≤ CR / u * shellModulus a kappa u s)
    (hprime : Nat.Prime (k + 2)) (hlow : ⌊Real.exp (kappa * u)⌋₊ < k + 2)
    (hhigh : k + 2 ≤ ⌊Real.exp (kappa * u + t)⌋₊) (ht : t ≤ L) :
    1 / 2 * shellModulus a kappa u t * Real.log ((k + 2 : ℕ) : ℝ)
      ≤ ((starRingEnd ℂ) (shellPhase a sigma kappa)
          * xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)).re := by
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hp0 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
  -- the two window inequalities in logarithmic form
  have hlogl : kappa * u < Real.log ((k + 2 : ℕ) : ℝ) := by
    have h1 := Nat.lt_floor_add_one (Real.exp (kappa * u))
    have h2 : ((⌊Real.exp (kappa * u)⌋₊ : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) := by
      exact_mod_cast hlow
    exact (Real.lt_log_iff_exp_lt hp0).2 (by linarith)
  have hlogh : Real.log ((k + 2 : ℕ) : ℝ) ≤ kappa * u + t := by
    have h1 : ((k + 2 : ℕ) : ℝ) ≤ ((⌊Real.exp (kappa * u + t)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hhigh
    have h2 : ((⌊Real.exp (kappa * u + t)⌋₊ : ℕ) : ℝ) ≤ Real.exp (kappa * u + t) :=
      Nat.floor_le (Real.exp_pos _).le
    exact (Real.log_le_iff_le_exp hp0).2 (le_trans h1 h2)
  have hs0 : 0 ≤ Real.log ((k + 2 : ℕ) : ℝ) - kappa * u := by linarith
  have hst : Real.log ((k + 2 : ℕ) : ℝ) - kappa * u ≤ t := by linarith
  have hsL : Real.log ((k + 2 : ℕ) : ℝ) - kappa * u ≤ L := le_trans hst ht
  have hlogeq : Real.log ((k + 2 : ℕ) : ℝ)
      = kappa * u + (Real.log ((k + 2 : ℕ) : ℝ) - kappa * u) := by ring
  have hatom := re_conj_phase_atom_ge (a := a) (sigma := sigma) hkappa hu hprime hlogeq
    (hrel _ hs0 hsL)
  refine le_trans ?_ hatom
  have hmono : shellModulus a kappa u t
      ≤ shellModulus a kappa u (Real.log ((k + 2 : ℕ) : ℝ) - kappa * u) :=
    shellModulus_antitone ha hkappa hu hst
  have hmodpos : 0 < shellModulus a kappa u (Real.log ((k + 2 : ℕ) : ℝ) - kappa * u) :=
    shellModulus_pos ha hkappa hu
  have hfac : (1 : ℝ) / 2 ≤ 1 - CR / u := by linarith
  have hhalf : 1 / 2 * shellModulus a kappa u (Real.log ((k + 2 : ℕ) : ℝ) - kappa * u)
      ≤ (1 - CR / u) * shellModulus a kappa u (Real.log ((k + 2 : ℕ) : ℝ) - kappa * u) :=
    mul_le_mul_of_nonneg_right hfac hmodpos.le
  have hkey : 1 / 2 * shellModulus a kappa u t
      ≤ (1 - CR / u) * shellModulus a kappa u (Real.log ((k + 2 : ℕ) : ℝ) - kappa * u) := by
    linarith
  have hlogpos : 0 ≤ Real.log ((k + 2 : ℕ) : ℝ) := by
    have := mul_pos hkappa0 hu
    linarith
  have := mul_le_mul_of_nonneg_left hkey hlogpos
  linarith

/-- The exterior block of a moving annulus, past the shifted cutoff `e^{κu+L}`. -/
theorem sum_norm_exteriorBlock_le {a sigma kappa u L : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma)
    (hkappa : 1 < kappa) (hu : 0 < u) (hL : 0 ≤ L) (N : ℕ) :
    ∑ k ∈ conePrimeIndex N \ conePrimeIndex ⌊Real.exp (kappa * u + L)⌋₊,
        ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)‖
      ≤ xiMassBesselExteriorSqrtTailConstant a sigma kappa / Real.sqrt u
        * Real.exp (-(xiMassBesselConeExponent a kappa * u))
        * Real.exp (-((a - 1 / 2) * L)) := by
  classical
  have hconv := sum_conePrimeIndex_sdiff_eq
    (M₀ := ⌊Real.exp (kappa * u + L)⌋₊) (M₁ := N)
    (g := fun p : ℕ => ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) p‖)
  rw [hconv]
  have hsub : (Finset.Ioc ⌊Real.exp (kappa * u + L)⌋₊ N).filter (fun p => Nat.Prime p)
      ⊆ (Nat.primesBelow (N + 1)).filter
          (fun p : ℕ => Real.exp (kappa * u + L) < (p : ℝ)) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hgt, hle⟩, hprime⟩ := hp
    rw [Finset.mem_filter, Nat.mem_primesBelow]
    refine ⟨⟨by omega, hprime⟩, ?_⟩
    have h1 := Nat.lt_floor_add_one (Real.exp (kappa * u + L))
    have h2 : ((⌊Real.exp (kappa * u + L)⌋₊ : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hgt
    linarith
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => norm_nonneg _) ?_
  exact sum_norm_xiMassCenteredPrimeAtom_exteriorSqrt_le ha hsigma hkappa hu hL N

/-- **Theorem 17.5.**  The moving prime annulus between two slopes is bounded below by the
stationary-phase amplitude. -/
theorem exists_subthreshold_annulus_lower_bound {a sigma kappa lam : ℝ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hkl : kappa < lam) :
    ∃ c u₀ : ℝ, 0 < c ∧ 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      c * (Real.exp (-(xiMassBesselConeExponent a kappa) * u) / Real.sqrt u)
        ≤ ‖xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope lam) u
            - xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u‖ := by
  classical
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hδ : (0 : ℝ) < a - 1 / 2 := by linarith
  have hlam : (1 : ℝ) < lam := lt_trans hkappa hkl
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hgap : (0 : ℝ) < lam - kappa := by linarith
  have hK₁ : 0 < shellAmplitude a kappa 1 := shellAmplitude_pos ha0 hkappa
  have hexp1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have hc₀ : (0 : ℝ) < 1 / 8 * (Real.exp 1 - 1) * shellAmplitude a kappa 1 := by
    have : (0 : ℝ) < Real.exp 1 - 1 := by linarith
    positivity
  have hCT : 0 ≤ xiMassBesselExteriorSqrtTailConstant a sigma kappa := by
    rw [xiMassBesselExteriorSqrtTailConstant]
    have h1 : 0 ≤ xiMassBesselExteriorSqrtConstant a sigma kappa :=
      xiMassBesselExteriorSqrtConstant_nonneg ha0 hkappa
    have h2 : 0 ≤ primeLogRpowTailConstant (a - 1 / 2) := primeLogRpowTailConstant_nonneg hδ
    have h3 : (0 : ℝ) < (2 : ℝ) ^ (a - 1 / 2) := Real.rpow_pos_of_pos (by norm_num) _
    exact mul_nonneg h1 (mul_nonneg h3.le h2)
  -- choose the window
  obtain ⟨L, hL1, hLbound⟩ : ∃ L : ℝ, 1 ≤ L ∧
      xiMassBesselExteriorSqrtTailConstant a sigma kappa * Real.exp (-((a - 1 / 2) * L))
        ≤ 1 / 8 * (Real.exp 1 - 1) * shellAmplitude a kappa 1 := by
    have hlim : Tendsto (fun L : ℝ =>
        xiMassBesselExteriorSqrtTailConstant a sigma kappa * Real.exp (-((a - 1 / 2) * L)))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun L : ℝ => -((a - 1 / 2) * L)) atTop atBot := by
        have h2 := Filter.tendsto_id.const_mul_atTop hδ
        have h3 : Tendsto (fun L : ℝ => -((a - 1 / 2) * L)) atTop atBot :=
          tendsto_neg_atTop_atBot.comp h2
        exact h3
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul
        (xiMassBesselExteriorSqrtTailConstant a sigma kappa)
    obtain ⟨L, hL⟩ := ((hlim.eventually_le_const hc₀).and (eventually_ge_atTop (1 : ℝ))).exists
    exact ⟨L, hL.2, hL.1⟩
  have hL0 : (0 : ℝ) ≤ L := le_trans zero_le_one hL1
  obtain ⟨CR, uR, hCR, huR, hrel⟩ := exists_shellProfile_relative_error ha0 hsigma hkappa hL0
  obtain ⟨uP, huP, hPNT⟩ := exists_shell_theta_lower hkappa0 zero_lt_one
  refine ⟨1 / 8 * (Real.exp 1 - 1) * shellAmplitude a kappa 1,
    max (max uR uP) (max (2 * CR) (max (L / (lam - kappa)) 1)), hc₀, ?_, fun u hu => ?_⟩
  · have : (0 : ℝ) < max (2 * CR) (max (L / (lam - kappa)) 1) :=
      lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) (le_max_right _ _))
    exact lt_of_lt_of_le this (le_max_right _ _)
  -- the height bounds
  have huR' : uR ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu
  have huP' : uP ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu
  have hCRu : 2 * CR ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hu
  have hLu : L / (lam - kappa) ≤ u :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hu)
  have hu1 : (1 : ℝ) ≤ u :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hu)
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
  have hCRhalf : CR / u ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hu0 (by norm_num)]
    linarith [hCRu]
  have hshift : kappa * u + L ≤ lam * u := by
    rw [div_le_iff₀ hgap] at hLu
    nlinarith [hLu]
  -- the four cutoffs of the annulus
  have hfl01 : ⌊Real.exp (kappa * u)⌋₊ ≤ ⌊Real.exp (kappa * u + 1)⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.2 (by linarith))
  have hfl1L : ⌊Real.exp (kappa * u + 1)⌋₊ ≤ ⌊Real.exp (kappa * u + L)⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.2 (by linarith))
  have hflLlam : ⌊Real.exp (kappa * u + L)⌋₊ ≤ ⌊Real.exp (lam * u)⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.2 hshift)
  have hE0 : (0 : ℝ) ≤ Real.exp (-(xiMassBesselConeExponent a kappa) * u) / Real.sqrt u := by
    positivity
  have hS1pos : 0 < shellModulus a kappa u 1 := shellModulus_pos ha0 hkappa hu0
  have hrelu := hrel u huR'
  -- the annulus as a phase-projected atom sum
  have hRe : ((starRingEnd ℂ) (shellPhase a sigma kappa)
      * (xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope lam) u
        - xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u)).re
      = ∑ k ∈ conePrimeIndex ⌊Real.exp (lam * u)⌋₊ \ conePrimeIndex ⌊Real.exp (kappa * u)⌋₊,
          ((starRingEnd ℂ) (shellPhase a sigma kappa)
            * xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)).re := by
    rw [annulus_eq_atom_sum hkappa hlam hkl.le hu0.le, Finset.mul_sum, Complex.re_sum]
  -- the three blocks
  have hsplit : ∑ k ∈ conePrimeIndex ⌊Real.exp (lam * u)⌋₊
        \ conePrimeIndex ⌊Real.exp (kappa * u)⌋₊,
        ((starRingEnd ℂ) (shellPhase a sigma kappa)
          * xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)).re
      = (∑ k ∈ conePrimeIndex ⌊Real.exp (kappa * u + 1)⌋₊
            \ conePrimeIndex ⌊Real.exp (kappa * u)⌋₊,
          ((starRingEnd ℂ) (shellPhase a sigma kappa)
            * xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)).re)
        + ((∑ k ∈ conePrimeIndex ⌊Real.exp (kappa * u + L)⌋₊
              \ conePrimeIndex ⌊Real.exp (kappa * u + 1)⌋₊,
            ((starRingEnd ℂ) (shellPhase a sigma kappa)
              * xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)).re)
          + ∑ k ∈ conePrimeIndex ⌊Real.exp (lam * u)⌋₊
              \ conePrimeIndex ⌊Real.exp (kappa * u + L)⌋₊,
            ((starRingEnd ℂ) (shellPhase a sigma kappa)
              * xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)).re) := by
    rw [conePrimeIndex_sdiff_split hfl01 (le_trans hfl1L hflLlam),
      conePrimeIndex_sdiff_split hfl1L hflLlam]
  -- the innermost unit shell
  have hblock1 : 2 * (1 / 8 * (Real.exp 1 - 1) * shellAmplitude a kappa 1)
        * (Real.exp (-(xiMassBesselConeExponent a kappa) * u) / Real.sqrt u)
      ≤ ∑ k ∈ conePrimeIndex ⌊Real.exp (kappa * u + 1)⌋₊
          \ conePrimeIndex ⌊Real.exp (kappa * u)⌋₊,
          ((starRingEnd ℂ) (shellPhase a sigma kappa)
            * xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)).re := by
    have hterm : ∀ k ∈ conePrimeIndex ⌊Real.exp (kappa * u + 1)⌋₊
        \ conePrimeIndex ⌊Real.exp (kappa * u)⌋₊,
        1 / 2 * shellModulus a kappa u 1 * Real.log ((k + 2 : ℕ) : ℝ)
          ≤ ((starRingEnd ℂ) (shellPhase a sigma kappa)
              * xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)).re := by
      intro k hk
      rw [Finset.mem_sdiff, mem_conePrimeIndex, mem_conePrimeIndex] at hk
      obtain ⟨⟨hle, hprime⟩, hnot⟩ := hk
      have hgt : ⌊Real.exp (kappa * u)⌋₊ < k + 2 := by
        by_contra hcon
        exact hnot ⟨by omega, hprime⟩
      exact re_conj_phase_atom_window ha0 hkappa hu0 hCRhalf hrelu hprime hgt hle hL1
    refine le_trans ?_ (Finset.sum_le_sum hterm)
    rw [← Finset.mul_sum]
    have hsum : ∑ k ∈ conePrimeIndex ⌊Real.exp (kappa * u + 1)⌋₊
        \ conePrimeIndex ⌊Real.exp (kappa * u)⌋₊, Real.log ((k + 2 : ℕ) : ℝ)
        = Chebyshev.theta (Real.exp (kappa * u + 1))
          - Chebyshev.theta (Real.exp (kappa * u)) := by
      rw [chebyshevTheta_sub_eq_shellSum hfl01]
      exact sum_conePrimeIndex_sdiff_eq (g := fun p : ℕ => Real.log (p : ℝ))
    rw [hsum]
    have hmass : shellModulus a kappa u 1 * Real.exp (kappa * u)
        = shellAmplitude a kappa 1
          * (Real.exp (-(xiMassBesselConeExponent a kappa) * u) / Real.sqrt u) :=
      shellModulus_mul_exp ha0 hkappa hu0
    have hstep : 1 / 2 * shellModulus a kappa u 1
        * ((1 / 2) * (Real.exp 1 - 1) * Real.exp (kappa * u))
        ≤ 1 / 2 * shellModulus a kappa u 1
          * (Chebyshev.theta (Real.exp (kappa * u + 1))
            - Chebyshev.theta (Real.exp (kappa * u))) :=
      mul_le_mul_of_nonneg_left (hPNT u huP') (by linarith)
    refine le_trans (le_of_eq ?_) hstep
    have hfold : 1 / 2 * shellModulus a kappa u 1
        * ((1 / 2) * (Real.exp 1 - 1) * Real.exp (kappa * u))
        = 1 / 4 * (Real.exp 1 - 1) * (shellModulus a kappa u 1 * Real.exp (kappa * u)) := by
      ring
    rw [hfold, hmass]
    ring
  -- the middle block is nonnegative
  have hblock2 : (0 : ℝ) ≤ ∑ k ∈ conePrimeIndex ⌊Real.exp (kappa * u + L)⌋₊
        \ conePrimeIndex ⌊Real.exp (kappa * u + 1)⌋₊,
        ((starRingEnd ℂ) (shellPhase a sigma kappa)
          * xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)).re := by
    refine Finset.sum_nonneg fun k hk => ?_
    rw [Finset.mem_sdiff, mem_conePrimeIndex, mem_conePrimeIndex] at hk
    obtain ⟨⟨hle, hprime⟩, hnot⟩ := hk
    have hgt1 : ⌊Real.exp (kappa * u + 1)⌋₊ < k + 2 := by
      by_contra hcon
      exact hnot ⟨by omega, hprime⟩
    have hgt : ⌊Real.exp (kappa * u)⌋₊ < k + 2 := lt_of_le_of_lt hfl01 hgt1
    have hwin := re_conj_phase_atom_window (t := L) ha0 hkappa hu0 hCRhalf hrelu hprime hgt hle
      le_rfl
    have hmodpos : 0 < shellModulus a kappa u L := shellModulus_pos ha0 hkappa hu0
    have hlogpos : 0 ≤ Real.log ((k + 2 : ℕ) : ℝ) := by
      have h1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
        have : (1 : ℕ) ≤ k + 2 := by omega
        exact_mod_cast this
      exact Real.log_nonneg h1
    have : (0 : ℝ) ≤ 1 / 2 * shellModulus a kappa u L * Real.log ((k + 2 : ℕ) : ℝ) := by
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 * shellModulus a kappa u L) hlogpos
      linarith
    linarith
  -- the exterior block
  have hblock3 : -((1 / 8 * (Real.exp 1 - 1) * shellAmplitude a kappa 1)
        * (Real.exp (-(xiMassBesselConeExponent a kappa) * u) / Real.sqrt u))
      ≤ ∑ k ∈ conePrimeIndex ⌊Real.exp (lam * u)⌋₊
          \ conePrimeIndex ⌊Real.exp (kappa * u + L)⌋₊,
          ((starRingEnd ℂ) (shellPhase a sigma kappa)
            * xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)).re := by
    have hlb : ∀ k ∈ conePrimeIndex ⌊Real.exp (lam * u)⌋₊
        \ conePrimeIndex ⌊Real.exp (kappa * u + L)⌋₊,
        -‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)‖
          ≤ ((starRingEnd ℂ) (shellPhase a sigma kappa)
              * xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)).re := by
      intro k _
      have h1 := Complex.abs_re_le_norm ((starRingEnd ℂ) (shellPhase a sigma kappa)
        * xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2))
      have h2 : ‖(starRingEnd ℂ) (shellPhase a sigma kappa)
          * xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)‖
          = ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)‖ := by
        rw [norm_mul, RCLike.norm_conj, norm_shellPhase, one_mul]
      rw [h2] at h1
      linarith [(abs_le.1 h1).1]
    refine le_trans ?_ (Finset.sum_le_sum hlb)
    rw [Finset.sum_neg_distrib, neg_le_neg_iff]
    have htail := sum_norm_exteriorBlock_le (a := a) (sigma := sigma) (kappa := kappa) (u := u)
      (L := L) ha hsigma hkappa hu0 hL0 ⌊Real.exp (lam * u)⌋₊
    refine le_trans htail ?_
    have hrw : xiMassBesselExteriorSqrtTailConstant a sigma kappa / Real.sqrt u
        * Real.exp (-(xiMassBesselConeExponent a kappa * u))
        * Real.exp (-((a - 1 / 2) * L))
        = (xiMassBesselExteriorSqrtTailConstant a sigma kappa
            * Real.exp (-((a - 1 / 2) * L)))
          * (Real.exp (-(xiMassBesselConeExponent a kappa) * u) / Real.sqrt u) := by
      rw [show -(xiMassBesselConeExponent a kappa) * u
          = -(xiMassBesselConeExponent a kappa * u) from by ring]
      ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right hLbound hE0
  -- the phase projection is dominated by the norm
  have hnormge : ((starRingEnd ℂ) (shellPhase a sigma kappa)
      * (xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope lam) u
        - xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u)).re
      ≤ ‖xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope lam) u
          - xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u‖ := by
    have h1 := Complex.abs_re_le_norm ((starRingEnd ℂ) (shellPhase a sigma kappa)
      * (xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope lam) u
        - xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u))
    have h2 : ‖(starRingEnd ℂ) (shellPhase a sigma kappa)
        * (xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope lam) u
          - xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u)‖
        = ‖xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope lam) u
            - xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u‖ := by
      rw [norm_mul, RCLike.norm_conj, norm_shellPhase, one_mul]
    rw [h2] at h1
    linarith [(abs_le.1 h1).2]
  rw [hRe, hsplit] at hnormge
  linarith

end

end RHTower
