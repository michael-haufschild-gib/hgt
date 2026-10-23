/-
The matched covariance profile and the Langevin intensity — the computable
half of the near-line zero-intensity route.

For the matched partial-sum field, the covariance profile has the limit shape
`K∞(u) = (1 − e^{−2u})/(2u)` in the rescaled coordinate `u = (σ − ½)·log N`,
the near-line zero intensity is `4π·ρ(u) = (log K∞)″(u)`, and the integrated
rate is the Langevin function `ε(c) = (coth c − 1/c)/(4π)`.  The exact
identities, on the `rcoth`/`rcsch` infrastructure of `CothInfra`:

* `log_matchedProfile_hasDerivAt` — `(log K∞)′(u) = langevin u − 1`, the
  closed form `coth u − 1/u − 1`;
* `langevin_hasDerivAt` — `L′(u) = 1/u² − 1/sinh²u` at every `u ≠ 0`, and
  `langevin_deriv_eq_intensity` — `L′ = 4π·matchedIntensity`: the intensity
  is the second log-derivative of the profile;
* `matchedIntensity_nonneg` — `ρ ≥ 0` at every `u ≠ 0` (`sinh²u ≥ u²`): a
  genuine point-process intensity.

The analytic open core — Steinhaus-vs-Gaussian local universality of the
near-line zero count — is typed as the explicit interface
`RouteAUniversality`; everything downstream of it here is proved.
-/
import GaloisForLFunctions.RHTower.CothInfra

namespace RHTower

open Real

/-- The matched covariance limit profile `K∞(u) = (1 − e^{−2u})/(2u)`: the
limit of `K(½ + u/log N)/log N` for the matched truncation. -/
noncomputable def matchedProfile (u : ℝ) : ℝ := (1 - Real.exp (-2 * u)) / (2 * u)

/-- The Langevin function `L(c) = coth c − 1/c`; the integrated near-line
rate is `ε(c) = L(c)/(4π)`. -/
noncomputable def langevin (c : ℝ) : ℝ := rcoth c - 1 / c

/-- The rescaled near-line zero intensity
`ρ(u) = (1/u² − 1/sinh²u)/(4π) = (log K∞)″(u)/(4π)`. -/
noncomputable def matchedIntensity (u : ℝ) : ℝ :=
  (1 / u ^ 2 - 1 / Real.sinh u ^ 2) / (4 * Real.pi)

private theorem exp_neg_two_mul_lt_one {u : ℝ} (hu : 0 < u) : Real.exp (-2 * u) < 1 := by
  rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
  exact Real.exp_lt_exp.mpr (by linarith)

/-- The profile is positive at every `u ≠ 0`: numerator and denominator of
`K∞` share their sign. -/
theorem matchedProfile_pos {u : ℝ} (hu : u ≠ 0) : 0 < matchedProfile u := by
  unfold matchedProfile
  rcases lt_or_gt_of_ne hu with h | h
  · have h1 : 1 < Real.exp (-2 * u) := by
      rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
      exact Real.exp_lt_exp.mpr (by linarith)
    exact div_pos_iff.mpr (Or.inr ⟨by linarith, by linarith⟩)
  · have h1 : Real.exp (-2 * u) < 1 := exp_neg_two_mul_lt_one h
    positivity

/-- **The log-profile derivative closed form:**
`(log K∞)′(u) = coth u − 1/u − 1 = langevin u − 1`. -/
theorem log_matchedProfile_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v => Real.log (matchedProfile v)) (langevin u - 1) u := by
  have hfne : (1 : ℝ) - Real.exp (-2 * u) ≠ 0 := by
    have := exp_neg_two_mul_lt_one hu
    linarith
  have hf : HasDerivAt (fun v : ℝ => 1 - Real.exp (-2 * v))
      (0 - Real.exp (-2 * u) * (-2 * 1)) u :=
    (hasDerivAt_const u (1 : ℝ)).sub (((hasDerivAt_id u).const_mul (-2 : ℝ)).exp)
  have hlogf := hf.log hfne
  have hg : HasDerivAt (fun v : ℝ => 2 * v) ((2 : ℝ) * 1) u :=
    (hasDerivAt_id u).const_mul 2
  have hlogg := hg.log (by positivity : (2 : ℝ) * u ≠ 0)
  have hsub := hlogf.sub hlogg
  have heq : (fun v => Real.log (matchedProfile v))
      =ᶠ[nhds u] fun v => Real.log (1 - Real.exp (-2 * v)) - Real.log (2 * v) := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    have hv0 : (0 : ℝ) < v := hv
    have h1 : Real.exp (-2 * v) < 1 := exp_neg_two_mul_lt_one hv0
    unfold matchedProfile
    rw [Real.log_div (by linarith) (by positivity)]
  have hK := hsub.congr_of_eventuallyEq heq
  have hcoth : rcoth u - 1 = 2 * Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) := by
    have hE1 : (0 : ℝ) < Real.exp (2 * u) - 1 := by
      have h := Real.exp_lt_exp.mpr (show (0 : ℝ) < 2 * u by positivity)
      rw [Real.exp_zero] at h
      linarith
    have hmul : Real.exp (-2 * u) * Real.exp (2 * u) = 1 := by
      rw [← Real.exp_add]; norm_num
    rw [rcoth_sub_one hu, div_eq_div_iff hE1.ne' hfne]
    linear_combination (-2 : ℝ) * hmul
  have hval : (0 - Real.exp (-2 * u) * (-2 * 1)) / (1 - Real.exp (-2 * u))
      - (2 : ℝ) * 1 / (2 * u) = langevin u - 1 := by
    unfold langevin
    rw [show (0 - Real.exp (-2 * u) * (-2 * 1)) / (1 - Real.exp (-2 * u))
        = 2 * Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) by ring_nf]
    rw [← hcoth]
    field_simp
    ring
  rw [hval] at hK
  exact hK

/-- **The Langevin derivative is the intensity numerator:**
`L′(u) = 1/u² − 1/sinh²u` at every `u ≠ 0`. -/
theorem langevin_hasDerivAt {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt langevin (1 / u ^ 2 - 1 / Real.sinh u ^ 2) u := by
  have h1 : HasDerivAt (fun c : ℝ => 1 / c) (-(1 / u ^ 2)) u := by
    have := hasDerivAt_inv hu
    simpa [one_div] using this
  have h := (rcoth_hasDerivAt hu).sub h1
  have hval : -rcsch u ^ 2 - -(1 / u ^ 2) = 1 / u ^ 2 - 1 / Real.sinh u ^ 2 := by
    rw [rcsch, div_pow, one_pow]
    ring
  rw [hval] at h
  exact h

/-- The Langevin derivative in intensity normalization:
`L′(u) = 4π·ρ(u)`. -/
theorem langevin_deriv_eq_intensity {u : ℝ} :
    1 / u ^ 2 - 1 / Real.sinh u ^ 2 = 4 * Real.pi * matchedIntensity u := by
  unfold matchedIntensity
  field_simp

/-- **The intensity is nonnegative at every `u ≠ 0`** (`sinh²u ≥ u²`): ρ is a
genuine point-process intensity. -/
theorem matchedIntensity_nonneg {u : ℝ} (hu : u ≠ 0) :
    0 ≤ matchedIntensity u := by
  unfold matchedIntensity
  have h1 : u ^ 2 ≤ Real.sinh u ^ 2 := by
    rcases lt_or_gt_of_ne hu with h | h
    · have hs : Real.sinh u < u := by
        have hpos := Real.self_lt_sinh_iff.mpr (neg_pos.mpr h)
        rw [Real.sinh_neg] at hpos
        linarith
      nlinarith [hs, h]
    · have hs : u < Real.sinh u := Real.self_lt_sinh_iff.mpr h
      nlinarith [hs, h]
  have h2 : (0 : ℝ) < u ^ 2 := by positivity
  have h3 : 1 / Real.sinh u ^ 2 ≤ 1 / u ^ 2 :=
    one_div_le_one_div_of_le h2 h1
  have h5 : (0 : ℝ) ≤ 1 / u ^ 2 - 1 / Real.sinh u ^ 2 := by linarith
  exact div_nonneg h5 (by positivity)

/-- **The open analytic core, typed.**  Steinhaus-vs-Gaussian local
universality: the near-line zero count `count N c` (zeros with
`β − ½ ≥ c/log N` in a window of length `U N`) obeys the intensity law with
the Langevin rate.  This is the single analytic input the route owes;
everything downstream of it is proved above. -/
def RouteAUniversality (count : ℕ → ℝ → ℝ) (U : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∀ c > 0, ∀ᶠ N in Filter.atTop,
    count N c ≤ (langevin c / (4 * Real.pi) + ε) * U N * Real.log N

end RHTower

namespace RHTower

open Filter Topology

/-- **The matched carrier profile is trapped by its limit shape, effectively.**
At the matched coordinate `σ = ½ + u/log N`, the carrier σ-profile
`K_N(σ) = ∑_{n ≤ N} n^{-2σ}` (the diagonal of `secondMoment_sigma`) satisfies

    log N · K∞(u)  ≤  K_N(½ + u/log N)  ≤  log N · K∞(u) + 1 :

the summand is `n^{-1-ε}` with `ε = 2u/log N`, the antitone sum–integral
comparison traps `K_N` between `∫₁^N x^{-1-ε} dx` and `1 + ∫₁^N x^{-1-ε} dx`,
and at the matched coordinate the integral is EXACTLY `log N · K∞(u)` because
`N^{-ε} = e^{-2u}`. -/
theorem carrier_profile_matched_bounds {u : ℝ} (hu : 0 < u) {N : ℕ} (hN : 2 ≤ N) :
    Real.log N * matchedProfile u
        ≤ (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * (1 / 2 + u / Real.log N)))
      ∧ (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * (1 / 2 + u / Real.log N)))
        ≤ Real.log N * matchedProfile u + 1 := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hN
  have hL : 0 < Real.log N := Real.log_pos hN1
  set ε := 2 * u / Real.log N with hε_def
  have hε : 0 < ε := by positivity
  set f : ℝ → ℝ := fun x => x ^ (-(1 + ε)) with hf_def
  set g : ℕ → ℝ := fun n => ((n : ℝ)) ^ (-(1 + ε)) with hg_def
  have hexp : ∀ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * (1 / 2 + u / Real.log N)) = g n := by
    intro n _
    rw [hg_def]
    congr 1
    rw [hε_def]
    ring
  rw [Finset.sum_congr rfl hexp]
  -- the antitone comparison function on [1, N]
  have hcast : (1 : ℝ) + ((N - 1 : ℕ) : ℝ) = (N : ℝ) := by
    have h1 : (1 : ℕ) ≤ N := by omega
    rw [Nat.cast_sub h1]
    push_cast
    ring
  have hanti : AntitoneOn f (Set.Icc (1 : ℝ) (1 + ((N - 1 : ℕ) : ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos hx.1) hxy
      (by linarith [hε])
  -- the exact integral: ∫₁^N x^{-1-ε} = log N · K∞(u)
  have hr : -(1 + ε) ≠ -1 := by
    intro h
    have : ε = 0 := by linarith
    exact hε.ne' this
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ) := by
    rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ (N : ℝ))]
    rintro ⟨h01, -⟩
    linarith
  have hNε : (N : ℝ) ^ (-ε) = Real.exp (-2 * u) := by
    rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < (N : ℝ))]
    congr 1
    rw [hε_def]
    field_simp
  have hint : (∫ x in (1 : ℝ)..(N : ℝ), f x) = Real.log N * matchedProfile u := by
    rw [hf_def]
    rw [integral_rpow (Or.inr ⟨hr, h0⟩)]
    have he : -(1 + ε) + 1 = -ε := by ring
    rw [he, Real.one_rpow, hNε, matchedProfile, hε_def]
    field_simp
    ring
  -- bridge the range-indexed comparison sums to Icc-indexed carrier sums
  have hbr1 : (∑ n ∈ Finset.Ico 1 N, g n) = ∑ i ∈ Finset.range (N - 1), f (1 + (i : ℝ)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hg_def, hf_def]
    push_cast
    ring_nf
  have hbr2 : (∑ n ∈ Finset.Icc 2 N, g n)
      = ∑ i ∈ Finset.range (N - 1), f (1 + ((i + 1 : ℕ) : ℝ)) := by
    have hIcoIcc : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcoIcc, Finset.sum_Ico_eq_sum_range]
    have hidx : N + 1 - 2 = N - 1 := by omega
    rw [hidx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hg_def, hf_def]
    push_cast
    ring_nf
  -- split off the first term of the carrier sum
  have hsplit : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hg1 : g 1 = 1 := by rw [hg_def]; push_cast; exact Real.one_rpow _
  have hS : (∑ n ∈ Finset.Icc 1 N, g n) = 1 + ∑ n ∈ Finset.Icc 2 N, g n := by
    rw [hsplit, Finset.sum_insert (by simp), hg1]
  constructor
  · -- lower: log N · K∞ = ∫ ≤ Σ_{Ico 1 N} ≤ Σ_{Icc 1 N}
    have hcomp := hanti.integral_le_sum
    rw [hcast] at hcomp
    have hsub : (∑ n ∈ Finset.Ico 1 N, g n) ≤ ∑ n ∈ Finset.Icc 1 N, g n :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self
        (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    calc Real.log N * matchedProfile u = ∫ x in (1 : ℝ)..(N : ℝ), f x := hint.symm
      _ ≤ ∑ i ∈ Finset.range (N - 1), f (1 + (i : ℝ)) := hcomp
      _ = ∑ n ∈ Finset.Ico 1 N, g n := hbr1.symm
      _ ≤ ∑ n ∈ Finset.Icc 1 N, g n := hsub
  · -- upper: Σ_{Icc 1 N} = 1 + Σ_{Icc 2 N} ≤ 1 + ∫ = log N · K∞ + 1
    have hcomp := hanti.sum_le_integral
    rw [hcast] at hcomp
    calc (∑ n ∈ Finset.Icc 1 N, g n) = 1 + ∑ n ∈ Finset.Icc 2 N, g n := hS
      _ = 1 + ∑ i ∈ Finset.range (N - 1), f (1 + ((i + 1 : ℕ) : ℝ)) := by rw [hbr2]
      _ ≤ 1 + ∫ x in (1 : ℝ)..(N : ℝ), f x := by
          have := hcomp
          linarith [this]
      _ = Real.log N * matchedProfile u + 1 := by rw [hint]; ring

/-- **The matched profile is the carrier's profile limit**: in the matched
coordinate `σ = ½ + u/log N`, the normalized carrier σ-profile
`K_N(σ)/log N` converges to `K∞(u) = matchedProfile u`, with the `1/log N`
error rate of `carrier_profile_matched_bounds`. -/
theorem tendsto_carrier_profile_matched {u : ℝ} (hu : 0 < u) :
    Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * (1 / 2 + u / Real.log N)))
          / Real.log N)
      atTop (nhds (matchedProfile u)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun N : ℕ => 1 / Real.log N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero' (Eventually.of_forall fun N => dist_nonneg) ?_ hlim
  filter_upwards [eventually_ge_atTop 2] with N hN
  obtain ⟨hlo, hhi⟩ := carrier_profile_matched_bounds hu hN
  have hL : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN)
  set S := ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * (1 / 2 + u / Real.log N))
  have h1 : matchedProfile u ≤ S / Real.log N := by
    rw [le_div_iff₀ hL]
    linarith
  have h2 : S / Real.log N - matchedProfile u ≤ 1 / Real.log N := by
    rw [sub_le_iff_le_add, div_le_iff₀ hL, add_mul, div_mul_cancel₀ _ hL.ne']
    linarith
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

end RHTower
