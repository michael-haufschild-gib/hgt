import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenGeometricEndpointBands
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowRelaxedPaperScale

/-!
# Grid-free certificate for the rooted minimal geometric schedule

The schedule uses width `δ_(A+1)`.  Its two rounding factors fit within `δ_A`, so both endpoint
collars and every lower-prime fibre satisfy the existing paper-scale certificate exactly.
-/

namespace RHTower.Sieve

open Filter Topology Finset

noncomputable section

private theorem mtLowerCutoff_div_one_add_le_sub_one
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

/-- Every sufficiently large paper scale admits the complete certificate for any initial
geometric level in the canonical one-step bracket. -/
theorem eventually_exists_minimalGeometricRootedPaperScaleCertificate
    (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (start z₁ : ℕ)
      (hz₀Q : (mtLowerCutoffNat X : ℝ) ≤
        mtGeometricLevel (mtPaperWidth (A + 1) X) start 0)
      (hQUpper : mtGeometricLevel (mtPaperWidth (A + 1) X) start 0 ≤
        (mtLowerCutoffNat X : ℝ) * (1 + mtPaperWidth (A + 1) X))
      (hroot : mtGeometricLevel (mtPaperWidth (A + 1) X) start 0 < (z₁ : ℝ))
      (hz₁X : (z₁ : ℝ) ≤ X)
      (hdelta : 0 < mtPaperWidth (A + 1) X),
      ∃ _cert : MTGridFreePaperScaleCertificate
        (MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
          (mtLowerCutoffNat X) (mtTruncationNat X) start z₁
          (mtPaperWidth (A + 1) X) hdelta hz₀Q hroot) A X, True := by
  filter_upwards [eventually_mtC1_integer_schedule,
    eventually_one_le_mtPaperWidth_mul_mtLowerCutoffNat_sub_one (A + 1),
    eventually_one_add_mtPaperWidth_succ_sq_le A,
    eventually_sum_inv_primesIco_relaxedPaperCutoff A,
    Filter.eventually_ge_atTop (Real.exp 1)]
      with X hschedule hprogress hwidthSq hmassX hX
  intro start z₁ hz₀Q hQUpper hroot hz₁X hdeltaRaw
  let delta := mtPaperWidth (A + 1) X
  let width := mtPaperWidth A X
  let z₀ := mtLowerCutoffNat X
  have hlog : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hdelta : 0 < delta := by simpa [delta] using hdeltaRaw
  have hdelta0 : 0 ≤ delta := hdelta.le
  have hwidth0 : 0 ≤ width := by
    dsimp [width, mtPaperWidth]
    exact Real.rpow_nonneg (zero_le_one.trans hlog) _
  have hz₀Two : 2 ≤ z₀ := by simpa [z₀] using hschedule.1
  have hz₀One : 1 ≤ z₀ := hz₀Two.trans' (by omega)
  have hz₀z₁ : z₀ ≤ z₁ := by
    have hzlt : (z₀ : ℝ) < (z₁ : ℝ) := hz₀Q.trans_lt hroot
    exact_mod_cast hzlt.le
  let t := mtMinimalGeometricDepth delta start (z₁ : ℝ) hdelta
  let endpoint := mtMinimalGeometricEndpoint delta start
  let data := MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
    z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot
  have hmono : Monotone endpoint := mtMinimalGeometricEndpoint_monotone hdelta start
  have hz₀Endpoint : z₀ ≤ endpoint 0 := by
    exact (Nat.le_floor hz₀Q).trans (Nat.le_add_right _ _)
  have hEndpointRoot : endpoint 0 ≤ z₁ := by
    have hfloor : Nat.floor (mtGeometricLevel delta start 0) < z₁ :=
      (Nat.floor_lt (mtGeometricLevel_pos hdelta start 0).le).mpr hroot
    dsimp [endpoint, mtMinimalGeometricEndpoint, mtRealBlockEndpoint]
    omega
  have hRootEndpoint : z₁ ≤ endpoint t := by
    have hspec := mtMinimalGeometricDepth_spec hdelta start (z₁ : ℝ)
    have hfloor : z₁ ≤ Nat.floor (mtGeometricLevel delta start t) := Nat.le_floor hspec
    exact hfloor.trans (Nat.le_add_right _ _)
  have hinitialBand : ((endpoint 0 - 1 : ℕ) : ℝ) ≤
      (1 + width) * ((z₀ - 1 : ℕ) : ℝ) := by
    exact mtGeometricInitialEndpoint_band hdelta0 hz₀One
      (by simpa [delta, z₀] using hprogress) hQUpper
      (by simpa [delta, width] using hwidthSq)
  have hterminalBand : ((endpoint t - 1 : ℕ) : ℝ) ≤
      (1 + width) * ((z₁ - 1 : ℕ) : ℝ) := by
    simpa [t, endpoint] using mtGeometricTerminalEndpoint_band hdelta hz₀One hz₀z₁
      hroot (by simpa [delta, z₀] using hprogress)
      (by simpa [delta, width] using hwidthSq)
  have hdeltaLeWidth : delta ≤ width := by
    have hsquare : (1 + delta) ^ 2 ≤ 1 + width := by
      simpa [delta, width] using hwidthSq
    nlinarith [sq_nonneg delta]
  have hprogressSmall : 1 ≤ delta * ((z₀ - 1 : ℕ) : ℝ) := by
    simpa [delta, z₀] using hprogress
  have hprogressWidth : 1 ≤ width * ((z₀ - 1 : ℕ) : ℝ) :=
    hprogressSmall.trans
      (mul_le_mul_of_nonneg_right hdeltaLeWidth (Nat.cast_nonneg _))
  have hrelaxed₀ : mtLowerCutoff X / (1 + width) ≤ ((z₀ - 1 : ℕ) : ℝ) := by
    simpa [width, z₀] using mtLowerCutoff_div_one_add_le_sub_one
      (A := A) (X := X) (z₀ := z₀) rfl hz₀One
      (by simpa [width] using hwidth0) (by simpa [width] using hprogressWidth)
  have hsubRoot : z₀ - 1 ≤ z₁ - 1 := Nat.sub_le_sub_right hz₀z₁ 1
  have hrelaxedRoot : mtLowerCutoff X / (1 + width) ≤
      ((z₁ - 1 : ℕ) : ℝ) := hrelaxed₀.trans (by exact_mod_cast hsubRoot)
  have hmassLower : ∑ q ∈ primesIco z₀ (endpoint 0), 1 / (q : ℝ) ≤
      2 * width := hmassX hrelaxed₀ hz₀Endpoint hinitialBand
  have hmassUpper : ∑ q ∈ primesIco z₁ (endpoint t), 1 / (q : ℝ) ≤
      2 * width := hmassX hrelaxedRoot hRootEndpoint hterminalBand
  have hz₁One : 1 ≤ z₁ := hz₀One.trans hz₀z₁
  let lower : ℕ → ℕ := data.lower (Fin.last t)
  let PLower := primesIco z₀ (endpoint 0)
  let PUpper := primesIco z₁ (endpoint t)
  let P := primesIco z₀ z₁
  refine ⟨{
    lower := lower
    PLower := PLower
    PUpper := PUpper
    P := P
    N := z₁
    z₀_eq := rfl
    D_eq := rfl
    lower_eq := ?_
    lower_subset := ?_
    upper_subset := ?_
    prefix_subset := ?_
    lower_prime := ?_
    upper_prime := ?_
    prime := ?_
    N_one := hz₁One
    N_le := hz₁X
    prime_le := ?_
    lower_mass := ?_
    upper_mass := ?_
    lower_cut := ?_
    lower_le := ?_
    band := ?_
  }, trivial⟩
  · intro k
    exact MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_lower_eq
      z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot k (Fin.last t)
  · intro k
    exact MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_lowerSpill_subset
      z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot k
  · intro k
    exact MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_upperSpill_subset
      z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot k
  · intro k q hq
    have hq' := mem_primesIco.mp hq
    exact mem_primesIco.mpr ⟨hq'.1,
      hq'.2.1.trans_le
        (MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_cutoff_le_root
          z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot k), hq'.2.2⟩
  · intro q hq
    exact (mem_primesIco.mp hq).2.2
  · intro q hq
    exact (mem_primesIco.mp hq).2.2
  · intro q hq
    exact (mem_primesIco.mp hq).2.2
  · intro q hq
    exact (mem_primesIco.mp hq).2.1.le
  · simpa [PLower, width] using hmassLower
  · simpa [PUpper, width] using hmassUpper
  · intro q hq
    by_cases hblock : ∃ i : Fin t, q ∈ mtAdjacentPrimeBlock endpoint i
    · obtain ⟨i, hqi⟩ := hblock
      rw [show lower q = endpoint i.1 by
        exact MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_lower_eq_of_mem
          z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot
          (Fin.last t) i hqi]
      exact hrelaxed₀.trans (by
        exact_mod_cast Nat.sub_le_sub_right
          (hz₀Endpoint.trans (hmono (Nat.zero_le i.1))) 1)
    · rw [show lower q = z₀ by
        exact MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_lower_eq_of_not_mem
          z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot
          (Fin.last t) hblock]
      exact hrelaxed₀
  · intro q hq
    by_cases hblock : ∃ i : Fin t, q ∈ mtAdjacentPrimeBlock endpoint i
    · obtain ⟨i, hqi⟩ := hblock
      rw [show lower q = endpoint i.1 by
        exact MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_lower_eq_of_mem
          z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot
          (Fin.last t) i hqi]
      exact mtMinimalGeometricBlock_lower_le hdelta i hqi
    · rw [show lower q = z₀ by
        exact MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_lower_eq_of_not_mem
          z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot
          (Fin.last t) hblock]
      exact (mem_primesIco.mp hq).1
  · intro q hq
    by_cases hblock : ∃ i : Fin t, q ∈ mtAdjacentPrimeBlock endpoint i
    · obtain ⟨i, hqi⟩ := hblock
      rw [show lower q = endpoint i.1 by
        exact MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_lower_eq_of_mem
          z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot
          (Fin.last t) i hqi]
      exact mtMinimalGeometricBlock_band hdelta hz₀One hz₀Endpoint
        (by simpa [delta, z₀] using hprogress)
        (by simpa [delta, width] using hwidthSq) i hqi
    · rw [show lower q = z₀ by
        exact MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_lower_eq_of_not_mem
          z₀ (mtTruncationNat X) start z₁ delta hdelta hz₀Q hroot
          (Fin.last t) hblock]
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
      exact (by exact_mod_cast hqSub : ((q - 1 : ℕ) : ℝ) ≤
        ((endpoint 0 - 1 : ℕ) : ℝ)).trans hinitialBand

/-- Canonical first-above-cutoff exponent supplies the schedule bracket automatically. -/
theorem eventually_exists_canonicalMinimalGeometricRootedPaperScaleCertificate
    (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ z₁ : ℕ,
      (mtLowerCutoffNat X : ℝ) * (1 + mtPaperWidth (A + 1) X) < (z₁ : ℝ) →
      (z₁ : ℝ) ≤ X →
      ∃ (start : ℕ) (hdelta : 0 < mtPaperWidth (A + 1) X)
        (hz₀Q : (mtLowerCutoffNat X : ℝ) ≤
          mtGeometricLevel (mtPaperWidth (A + 1) X) start 0)
        (hroot : mtGeometricLevel (mtPaperWidth (A + 1) X) start 0 < (z₁ : ℝ)),
        ∃ _cert : MTGridFreePaperScaleCertificate
          (MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
            (mtLowerCutoffNat X) (mtTruncationNat X) start z₁
            (mtPaperWidth (A + 1) X) hdelta hz₀Q hroot) A X, True := by
  filter_upwards [eventually_exists_minimalGeometricRootedPaperScaleCertificate A,
    eventually_mtC1_integer_schedule, Filter.eventually_ge_atTop (Real.exp 1)]
      with X hcertX hschedule hX
  intro z₁ hroom hz₁X
  have hlog : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hdelta : 0 < mtPaperWidth (A + 1) X := by
    rw [mtPaperWidth]
    exact Real.rpow_pos_of_pos (zero_lt_one.trans_le hlog) _
  have hz₀One : 1 ≤ mtLowerCutoffNat X := by omega
  have hbracket := mtFirstGeometricStart_bracket hdelta hz₀One
  let start := mtFirstGeometricStart (mtPaperWidth (A + 1) X)
    (mtLowerCutoffNat X)
  have hz₀Q : (mtLowerCutoffNat X : ℝ) ≤
      mtGeometricLevel (mtPaperWidth (A + 1) X) start 0 := hbracket.1.le
  have hroot : mtGeometricLevel (mtPaperWidth (A + 1) X) start 0 < (z₁ : ℝ) :=
    hbracket.2.trans_lt hroom
  obtain ⟨cert, hcert⟩ := hcertX start z₁ hz₀Q hbracket.2 hroot hz₁X hdelta
  exact ⟨start, hdelta, hz₀Q, hroot, cert, hcert⟩

end

end RHTower.Sieve
