import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMinimalGeometricCeilRooted
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMinimalGeometricDilationCertificate

/-!
# Fixed-dilation certificate for the real-rooted schedule

The terminal cutoff is `ceil z₁`, but block depth is selected by the literal real root `z₁`.
Endpoint alignment removes all internal spills; initial and terminal collars obey the same
`4 δ_A` reciprocal-mass budget as the natural-rooted schedule.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction

noncomputable section

private theorem mtLowerCutoff_div_one_add_le_sub_one_ceilRooted
    {A : ℕ} {X : ℝ} {z₀ : ℕ}
    (hz₀ : z₀ = mtLowerCutoffNat X) (hz₀One : 1 ≤ z₀)
    (hwidth : 0 ≤ mtPaperWidth A X)
    (hprogress : 1 ≤ mtPaperWidth A X * ((z₀ - 1 : ℕ) : ℝ)) :
    mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((z₀ - 1 : ℕ) : ℝ) := by
  have hcutCeil : mtLowerCutoff X ≤ (z₀ : ℝ) := by
    rw [hz₀, mtLowerCutoffNat]
    exact Nat.le_ceil _
  have hden : 0 < 1 + mtPaperWidth A X := by linarith
  have hz₀Cast : (z₀ : ℝ) = ((z₀ - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub hz₀One]
    push_cast
    ring
  apply (div_le_iff₀ hden).2
  calc
    mtLowerCutoff X ≤ (z₀ : ℝ) := hcutCeil
    _ = ((z₀ - 1 : ℕ) : ℝ) + 1 := hz₀Cast
    _ ≤ ((z₀ - 1 : ℕ) : ℝ) +
        mtPaperWidth A X * ((z₀ - 1 : ℕ) : ℝ) := by
      simpa [add_comm] using add_le_add_left hprogress ((z₀ - 1 : ℕ) : ℝ)
    _ = ((z₀ - 1 : ℕ) : ℝ) * (1 + mtPaperWidth A X) := by ring

/-- Every sufficiently large scale admits the full fixed-dilation certificate for a geometric
schedule stopped at a literal real root and sifted at its natural ceiling. -/
theorem eventually_exists_minimalGeometricCeilRootedDilationCertificate
    (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (start : ℕ) (z₁ : ℝ)
      (hz₀Q : (mtLowerCutoffNat X : ℝ) ≤
        mtGeometricLevel (mtPaperWidth A X) start 0)
      (_hQUpper : mtGeometricLevel (mtPaperWidth A X) start 0 ≤
        (mtLowerCutoffNat X : ℝ) * (1 + mtPaperWidth A X))
      (hroot : mtGeometricLevel (mtPaperWidth A X) start 0 < z₁)
      (_hzNatX : (Nat.ceil z₁ : ℝ) ≤ X)
      (hdelta : 0 < mtPaperWidth A X),
      ∃ _cert : MTGridFreeDilationCertificate
        (MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
          (mtLowerCutoffNat X) (mtTruncationNat X) start z₁
          (mtPaperWidth A X) hdelta hz₀Q hroot) A X, True := by
  filter_upwards [eventually_mtC1_integer_schedule,
    eventually_one_le_mtPaperWidth_mul_mtLowerCutoffNat_sub_one A,
    eventually_sum_inv_primesIco_relaxedPaperCutoff_fixedDilation A 3 (by norm_num),
    Filter.eventually_ge_atTop (Real.exp 1)]
      with X hschedule hprogress hmassX hX
  intro start z₁ hz₀Q hQUpper hroot hzNatX hdeltaRaw
  let delta := mtPaperWidth A X
  let z₀ := mtLowerCutoffNat X
  let zNat := Nat.ceil z₁
  have hlog : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hdelta : 0 < delta := by simpa [delta] using hdeltaRaw
  have hdelta0 : 0 ≤ delta := hdelta.le
  have hdeltaOne : delta ≤ 1 := by
    dsimp [delta, mtPaperWidth]
    calc
      (Real.log X) ^ (-((10 * A : ℕ) : ℝ)) ≤ (Real.log X) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlog (neg_nonpos.mpr (Nat.cast_nonneg _))
      _ = 1 := by simp
  have hwidth : (1 + delta) ^ 2 ≤ 1 + 3 * delta := by
    nlinarith [mul_nonneg hdelta0 (sub_nonneg.mpr hdeltaOne)]
  have hz₀Two : 2 ≤ z₀ := by simpa [z₀] using hschedule.1
  have hz₀One : 1 ≤ z₀ := by omega
  have hz₀zNat : z₀ ≤ zNat := by
    have hzlt : (z₀ : ℝ) < (zNat : ℝ) :=
      hz₀Q.trans_lt (hroot.trans_le (Nat.le_ceil z₁))
    exact_mod_cast hzlt.le
  let t := mtMinimalGeometricDepth delta start z₁ hdelta
  let endpoint := mtMinimalGeometricEndpoint delta start
  let data := MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
    z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot
  have hmono : Monotone endpoint := mtMinimalGeometricEndpoint_monotone hdelta start
  have hz₀Endpoint : z₀ ≤ endpoint 0 := by
    exact (Nat.le_floor hz₀Q).trans (Nat.le_add_right _ _)
  have hEndpointRoot : endpoint 0 ≤ zNat := by
    have hfloor : Nat.floor (mtGeometricLevel delta start 0) < zNat :=
      (Nat.floor_lt (mtGeometricLevel_pos hdelta start 0).le).mpr
        (hroot.trans_le (Nat.le_ceil z₁))
    dsimp [endpoint, mtMinimalGeometricEndpoint, mtRealBlockEndpoint, zNat]
    omega
  have hRootEndpoint : zNat ≤ endpoint t := by
    have hspec := mtMinimalGeometricDepth_spec hdelta start z₁
    have hceil : Nat.ceil z₁ ≤ Nat.floor (mtGeometricLevel delta start t) + 1 := by
      apply (Nat.ceil_le).mpr
      have hfloor : mtGeometricLevel delta start t <
          ((Nat.floor (mtGeometricLevel delta start t) + 1 : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          Nat.lt_floor_add_one (mtGeometricLevel delta start t)
      exact hspec.trans_lt hfloor |>.le
    simpa [endpoint, mtMinimalGeometricEndpoint, mtRealBlockEndpoint, zNat] using hceil
  have hinitialBand : ((endpoint 0 - 1 : ℕ) : ℝ) ≤
      (1 + 3 * delta) * ((z₀ - 1 : ℕ) : ℝ) := by
    exact mtGeometricInitialEndpoint_band hdelta0 hz₀One
      (by simpa [delta, z₀] using hprogress) hQUpper hwidth
  have hterminalBand : ((endpoint t - 1 : ℕ) : ℝ) ≤
      (1 + 3 * delta) * ((zNat - 1 : ℕ) : ℝ) := by
    let tNat := mtMinimalGeometricDepth delta start (zNat : ℝ) hdelta
    have hrootNat : mtGeometricLevel delta start 0 < (zNat : ℝ) :=
      hroot.trans_le (by simpa [zNat] using Nat.le_ceil z₁)
    have httNat : t ≤ tNat := by
      by_contra hnot
      have htNatLt : tNat < t := Nat.lt_of_not_ge hnot
      have hlt := mtGeometricLevel_lt_of_lt_minimalDepth
        hdelta start z₁ htNatLt
      have hspecNat := mtMinimalGeometricDepth_spec hdelta start (zNat : ℝ)
      have hz₁zNat : z₁ ≤ (zNat : ℝ) := by simpa [zNat] using Nat.le_ceil z₁
      linarith
    have hendpointLe : endpoint t ≤ endpoint tNat := hmono httNat
    have hbandNat : ((endpoint tNat - 1 : ℕ) : ℝ) ≤
        (1 + 3 * delta) * ((zNat - 1 : ℕ) : ℝ) := by
      simpa [tNat, endpoint] using mtGeometricTerminalEndpoint_band
        hdelta hz₀One hz₀zNat hrootNat
        (by simpa [delta, z₀] using hprogress) hwidth
    have hsub : ((endpoint t - 1 : ℕ) : ℝ) ≤
        ((endpoint tNat - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le_sub_right hendpointLe 1
    exact hsub.trans hbandNat
  have hrelaxed₀ : mtLowerCutoff X / (1 + delta) ≤ ((z₀ - 1 : ℕ) : ℝ) := by
    simpa [delta, z₀] using mtLowerCutoff_div_one_add_le_sub_one_ceilRooted
      (A := A) (X := X) (z₀ := z₀) rfl hz₀One hdelta0
      (by simpa [delta, z₀] using hprogress)
  have hsubRoot : z₀ - 1 ≤ zNat - 1 := Nat.sub_le_sub_right hz₀zNat 1
  have hrelaxedRoot : mtLowerCutoff X / (1 + delta) ≤
      ((zNat - 1 : ℕ) : ℝ) := hrelaxed₀.trans (by exact_mod_cast hsubRoot)
  have hmassLower : ∑ q ∈ primesIco z₀ (endpoint 0), 1 / (q : ℝ) ≤
      4 * delta := by
    have hm := hmassX hrelaxed₀ hz₀Endpoint hinitialBand
    norm_num at hm
    simpa [delta] using hm
  have hmassUpper : ∑ q ∈ primesIco zNat (endpoint t), 1 / (q : ℝ) ≤
      4 * delta := by
    have hm := hmassX hrelaxedRoot hRootEndpoint hterminalBand
    norm_num at hm
    simpa [delta] using hm
  have hzNatOne : 1 ≤ zNat := hz₀One.trans hz₀zNat
  let lower : ℕ → ℕ := data.lower (Fin.last t)
  let PLower := primesIco z₀ (endpoint 0)
  let PUpper := primesIco zNat (endpoint t)
  let P := primesIco z₀ zNat
  refine ⟨{
    lower := lower
    PLower := PLower
    PUpper := PUpper
    P := P
    N := zNat
    z₀_eq := rfl
    D_eq := rfl
    lower_eq := ?_
    lower_subset := ?_
    upper_subset := ?_
    prefix_subset := ?_
    lower_prime := ?_
    upper_prime := ?_
    prime := ?_
    N_one := hzNatOne
    N_le := by simpa [zNat] using hzNatX
    prime_le := ?_
    lower_mass := ?_
    upper_mass := ?_
    lower_le := ?_
    fibre_mass := ?_
  }, trivial⟩
  · intro k
    exact MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_lower_eq
      z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot k (Fin.last t)
  · intro k
    exact MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_lowerSpill_subset
      z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot k
  · intro k
    exact MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_upperSpill_subset
      z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot k
  · intro k q hq
    have hq' := mem_primesIco.mp hq
    exact mem_primesIco.mpr ⟨hq'.1,
      hq'.2.1.trans_le
        (MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_cutoff_le_root
          z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot k), hq'.2.2⟩
  · intro q hq
    exact (mem_primesIco.mp hq).2.2
  · intro q hq
    exact (mem_primesIco.mp hq).2.2
  · intro q hq
    exact (mem_primesIco.mp hq).2.2
  · intro q hq
    exact (mem_primesIco.mp hq).2.1.le
  · simpa [PLower, delta] using hmassLower
  · simpa [PUpper, delta] using hmassUpper
  · intro q hq
    by_cases hblock : ∃ i : Fin t, q ∈ mtAdjacentPrimeBlock endpoint i
    · obtain ⟨i, hqi⟩ := hblock
      rw [show lower q = endpoint i.1 by
        exact MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_lower_eq_of_mem
          z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot
          (Fin.last t) i hqi]
      exact mtMinimalGeometricBlock_lower_le hdelta i hqi
    · rw [show lower q = z₀ by
        exact MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_lower_eq_of_not_mem
          z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot
          (Fin.last t) hblock]
      exact (mem_primesIco.mp hq).1
  · intro q hq
    by_cases hblock : ∃ i : Fin t, q ∈ mtAdjacentPrimeBlock endpoint i
    · obtain ⟨i, hqi⟩ := hblock
      have hlowerEq : lower q = endpoint i.1 :=
        MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_lower_eq_of_mem
          z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot
          (Fin.last t) i hqi
      have hlowerCut : mtLowerCutoff X / (1 + delta) ≤
          ((endpoint i.1 - 1 : ℕ) : ℝ) := hrelaxed₀.trans (by
        exact_mod_cast Nat.sub_le_sub_right
          (hz₀Endpoint.trans (hmono (Nat.zero_le i.1))) 1)
      have hband : ((q - 1 : ℕ) : ℝ) ≤
          (1 + 3 * delta) * ((endpoint i.1 - 1 : ℕ) : ℝ) :=
        mtMinimalGeometricBlock_band hdelta hz₀One hz₀Endpoint
          (by simpa [delta, z₀] using hprogress) hwidth i hqi
      rw [hlowerEq]
      have hm := hmassX hlowerCut
        (mtMinimalGeometricBlock_lower_le hdelta i hqi) hband
      norm_num at hm
      simpa [delta] using hm
    · have hlowerEq : lower q = z₀ :=
        MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_lower_eq_of_not_mem
          z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot
          (Fin.last t) hblock
      have hqData := mem_primesIco.mp hq
      have hqEndpoint : q < endpoint 0 := by
        by_contra hnot
        have hqUnion : q ∈ (mtBlockPrefix (Fin.last t)).biUnion
            (mtAdjacentPrimeBlock endpoint) := by
          rw [mtAdjacentPrimeBlock_prefix_biUnion endpoint hmono]
          exact mem_primesIco.mpr
            ⟨Nat.le_of_not_gt hnot, hqData.2.1.trans_le hRootEndpoint, hqData.2.2⟩
        obtain ⟨i, hi, hqi⟩ := Finset.mem_biUnion.mp hqUnion
        exact hblock ⟨i, hqi⟩
      have hqSub : q - 1 ≤ endpoint 0 - 1 := by omega
      have hband : ((q - 1 : ℕ) : ℝ) ≤
          (1 + 3 * delta) * ((z₀ - 1 : ℕ) : ℝ) := by
        have hqSubR : ((q - 1 : ℕ) : ℝ) ≤
            ((endpoint 0 - 1 : ℕ) : ℝ) := by exact_mod_cast hqSub
        exact hqSubR.trans hinitialBand
      rw [hlowerEq]
      have hm := hmassX hrelaxed₀ hqData.1 hband
      norm_num at hm
      simpa [delta] using hm

end

end RHTower.Sieve
