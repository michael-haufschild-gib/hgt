import GaloisForLFunctions.RHTower.CoherentKernelChart

/-!
# The prime-profile squarefree Fock limit

`prime-valuation-dyadic-fermion-normal-cone-law`, equations `(13p)`–`(13y)`.

The radial family `u ↦ ut` is only one line inside the complete normal experiment.  For an arbitrary
prime-scale profile `f` vanishing at the origin, put

`q_{p,x}(f) = p^{-1} e^{2 f(log p / log x)}`

and let `B_x(f,g)` be the Hellinger affinity of the corresponding product Bernoulli laws.  The same
mechanism as in the radial case — first-order cancellation in the parity digit, Mertens weak
convergence of the prime window, and a Tannery-dominated remainder — gives

`B_x(f,g) → K(f,g) = exp(-½ ∫₀¹ (e^{f(t)} - e^{g(t)})² dt/t)`.

The radial kernel is the specialization `f(t) = ut`, and the profile field is total in the
symmetric Fock space over `L²((0,1), dt/t)` because `G_{log(1+εφ)} = εφ`.
-/

open Filter Topology Set
open GaloisForLFunctions.HTGeometry

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The prime-scale profile nome `q_{p,x}(f) = p^{-1} e^{2 f(log p / log x)}`. -/
def profileNome (f : ℝ → ℝ) (N n : ℕ) : ℝ :=
  ((n : ℝ))⁻¹ * Real.exp (2 * f (Real.log n / Real.log N))

theorem profileNome_pos {f : ℝ → ℝ} {N n : ℕ} (hn : 2 ≤ n) : 0 < profileNome f N n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [profileNome]
  positivity

/-- The radial family is the linear profile. -/
theorem profileNome_linear (u : ℝ) (N n : ℕ) (hn : 2 ≤ n) :
    profileNome (fun t => u * t) N n = radialNome (u / Real.log N) n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [profileNome, radialNome_eq_exp hn]
  have hinv : ((n : ℝ))⁻¹ = Real.exp (-Real.log n) := by
    rw [Real.exp_neg, Real.exp_log hn0]
  rw [hinv, ← Real.exp_add]
  congr 1
  field_simp
  ring

theorem sqrt_profileNome {f : ℝ → ℝ} {N n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt (profileNome f N n)
      = Real.sqrt ((n : ℝ))⁻¹ * Real.exp (f (Real.log n / Real.log N)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hinv0 : (0 : ℝ) ≤ ((n : ℝ))⁻¹ := by positivity
  rw [profileNome, Real.sqrt_mul hinv0]
  congr 1
  rw [show (2 : ℝ) * f (Real.log n / Real.log N)
    = f (Real.log n / Real.log N) + f (Real.log n / Real.log N) by ring, Real.exp_add,
    ← sq, Real.sqrt_sq (Real.exp_nonneg _)]

/-- **The quadratic Hellinger displacement of a profile pair.** -/
theorem sq_sqrt_profileNome_sub {f g : ℝ → ℝ} {N n : ℕ} (hn : 2 ≤ n) :
    (Real.sqrt (profileNome f N n) - Real.sqrt (profileNome g N n)) ^ 2
      = (Real.exp (f (Real.log n / Real.log N)) - Real.exp (g (Real.log n / Real.log N))) ^ 2
        / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hinv : Real.sqrt ((n : ℝ))⁻¹ ^ 2 = ((n : ℝ))⁻¹ :=
    Real.sq_sqrt (by positivity)
  rw [sqrt_profileNome hn, sqrt_profileNome hn, ← mul_sub, mul_pow, hinv]
  ring

/-! ## The profile class and its uniform bounds -/

/-- The card's profile class `𝓕₀`: continuous on the unit prime-scale interval and vanishing at
the origin at linear rate `L`. -/
structure IsScaleProfile (f : ℝ → ℝ) (L : ℝ) : Prop where
  cont : ContinuousOn f (Set.Icc 0 1)
  slope : ∀ t ∈ Set.Icc 0 1, |f t| ≤ L * t

theorem IsScaleProfile.slope_nonneg {f : ℝ → ℝ} {L : ℝ} (hf : IsScaleProfile f L) : 0 ≤ L := by
  have h := hf.slope 1 (by constructor <;> norm_num)
  rw [mul_one] at h
  exact le_trans (abs_nonneg _) h

theorem IsScaleProfile.zero {f : ℝ → ℝ} {L : ℝ} (hf : IsScaleProfile f L) : f 0 = 0 := by
  have h := hf.slope 0 (by constructor <;> norm_num)
  rw [mul_zero] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

theorem logRatio_mem {N n : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N) :
    Real.log n / Real.log N ∈ Set.Icc (0 : ℝ) 1 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnN' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by linarith
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hlogN]
  exact Real.log_le_log (by linarith) hnN'

/-- Uniform decay of the profile nome once the cutoff dominates the slope. -/
theorem profileNome_le_exp {f : ℝ → ℝ} {L : ℝ} (hf : IsScaleProfile f L) {N n : ℕ}
    (hn : 2 ≤ n) (hnN : n ≤ N) (hNL : 16 * L ≤ Real.log N) (hN : 2 ≤ N) :
    profileNome f N n ≤ Real.exp (-(7 / 8) * Real.log n) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hL := hf.slope_nonneg
  have hbound := hf.slope _ (logRatio_mem hn hnN)
  have hle : 2 * f (Real.log n / Real.log N) ≤ (1 / 8) * Real.log n := by
    have h1 : f (Real.log n / Real.log N) ≤ L * (Real.log n / Real.log N) :=
      le_trans (le_abs_self _) hbound
    have h2 : L * (Real.log n / Real.log N) ≤ (1 / 16) * Real.log n := by
      rcases eq_or_lt_of_le hL with hL0 | hL0
      · rw [← hL0]
        simp
        positivity
      · have hlogN16 : 16 * L ≤ Real.log N := hNL
        rw [mul_div_assoc']
        rw [div_le_iff₀ hlogN]
        nlinarith [hlogn, hlogN, hL0]
    linarith
  have hinv : ((n : ℝ))⁻¹ = Real.exp (-Real.log n) := by
    rw [Real.exp_neg, Real.exp_log (by linarith)]
  rw [profileNome, hinv, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  linarith

theorem profileNome_le_three_quarters {f : ℝ → ℝ} {L : ℝ} (hf : IsScaleProfile f L) {N n : ℕ}
    (hn : 2 ≤ n) (hnN : n ≤ N) (hNL : 16 * L ≤ Real.log N) (hN : 2 ≤ N) :
    profileNome f N n ≤ 3 / 4 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog2 : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn2
  refine le_trans (profileNome_le_exp hf hn hnN hNL hN) ?_
  have hstep : Real.exp (-(7 / 8) * Real.log n) ≤ Real.exp (-(3 / 4) * Real.log 2) := by
    refine Real.exp_le_exp.mpr ?_
    have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [hlog2, hlog0]
  refine le_trans hstep ?_
  set y := Real.exp (-(3 / 4 : ℝ) * Real.log 2) with hy
  have hy0 : (0 : ℝ) < y := Real.exp_pos _
  have hy4 : y ^ 4 = 1 / 8 := by
    rw [hy, ← Real.exp_nat_mul]
    rw [show ((4 : ℕ) : ℝ) * (-(3 / 4 : ℝ) * Real.log 2) = -(3 * Real.log 2) by push_cast; ring]
    rw [show (3 : ℝ) * Real.log 2 = Real.log 8 by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring]
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  nlinarith [hy0, hy4, sq_nonneg (y - 3 / 4), sq_nonneg (y + 3 / 4), sq_nonneg (y * y - 9 / 16)]

theorem sq_profileNome_le {f : ℝ → ℝ} {L : ℝ} (hf : IsScaleProfile f L) {N n : ℕ}
    (hn : 2 ≤ n) (hnN : n ≤ N) (hNL : 16 * L ≤ Real.log N) (hN : 2 ≤ N) :
    profileNome f N n ^ 2 ≤ ((n : ℝ)) ^ (-(3 / 2 : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have h1 := profileNome_le_exp hf hn hnN hNL hN
  have h0 : 0 ≤ profileNome f N n := (profileNome_pos hn).le
  have hsq : profileNome f N n ^ 2 ≤ Real.exp (-(7 / 8) * Real.log n) ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  refine le_trans hsq ?_
  rw [← Real.exp_nat_mul]
  rw [show ((n : ℝ)) ^ (-(3 / 2 : ℝ)) = Real.exp (-(3 / 2) * Real.log n) by
    rw [Real.rpow_def_of_pos (by linarith)]; ring_nf]
  refine Real.exp_le_exp.mpr ?_
  push_cast
  linarith

/-! ## The profile coherent profile and its quotient -/

/-- The two-profile critical numerator `(e^{f(t)} - e^{g(t)})²`. -/
def profileCoherentProfile (f g : ℝ → ℝ) (t : ℝ) : ℝ := (Real.exp (f t) - Real.exp (g t)) ^ 2

theorem abs_exp_sub_exp_le {f g : ℝ → ℝ} {L : ℝ} (hf : IsScaleProfile f L) (hg : IsScaleProfile g L)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |Real.exp (f t) - Real.exp (g t)| ≤ 2 * L * Real.exp (3 * L) * t := by
  have hL := hf.slope_nonneg
  have hfb := hf.slope t ht
  have hgb := hg.slope t ht
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hgL : |g t| ≤ L := le_trans hgb (by nlinarith)
  have hdiff : |f t - g t| ≤ 2 * L * t := by
    have := abs_sub (f t) (g t)
    linarith
  have hdiffL : |f t - g t| ≤ 2 * L := le_trans hdiff (by nlinarith)
  have hfac : Real.exp (f t) - Real.exp (g t)
      = Real.exp (g t) * (Real.exp (f t - g t) - 1) := by
    rw [mul_sub, ← Real.exp_add, mul_one]
    congr 2
    ring
  rw [hfac, abs_mul]
  have h1 : |Real.exp (g t)| ≤ Real.exp L := by
    rw [abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) hgL)
  have h2 : |Real.exp (f t - g t) - 1| ≤ 2 * L * t * Real.exp (2 * L) := by
    refine le_trans (abs_exp_sub_one_le_mul (f t - g t)) ?_
    have hE : Real.exp |f t - g t| ≤ Real.exp (2 * L) := Real.exp_le_exp.mpr hdiffL
    have := mul_le_mul hdiff hE (Real.exp_nonneg _) (by positivity)
    exact this
  have hprod := mul_le_mul h1 h2 (abs_nonneg _) (Real.exp_nonneg _)
  refine le_trans hprod (le_of_eq ?_)
  rw [show (3 : ℝ) * L = L + 2 * L by ring, Real.exp_add]
  ring

theorem profileCoherentProfile_le {f g : ℝ → ℝ} {L : ℝ}
    (hf : IsScaleProfile f L) (hg : IsScaleProfile g L)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    profileCoherentProfile f g t ≤ (2 * L * Real.exp (3 * L)) ^ 2 * t ^ 2 := by
  have h := abs_exp_sub_exp_le hf hg ht
  have hsq : (Real.exp (f t) - Real.exp (g t)) ^ 2
      ≤ (2 * L * Real.exp (3 * L) * t) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [profileCoherentProfile]
  refine le_trans hsq (le_of_eq ?_)
  ring

theorem divProfile_profileCoherent_nonneg (f g : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ divProfile (profileCoherentProfile f g) t := by
  rw [divProfile]
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (by rw [profileCoherentProfile]; positivity) ht

theorem divProfile_profileCoherent_le {f g : ℝ → ℝ} {L : ℝ}
    (hf : IsScaleProfile f L) (hg : IsScaleProfile g L)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    divProfile (profileCoherentProfile f g) t ≤ (2 * L * Real.exp (3 * L)) ^ 2 * t := by
  rw [divProfile]
  split_ifs with h
  · rw [h]
    simp
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    rw [div_le_iff₀ htpos]
    refine le_trans (profileCoherentProfile_le hf hg ht) (le_of_eq ?_)
    ring

theorem continuousOn_divProfile_profileCoherent {f g : ℝ → ℝ} {L : ℝ}
    (hf : IsScaleProfile f L) (hg : IsScaleProfile g L) :
    ContinuousOn (divProfile (profileCoherentProfile f g)) (Set.Icc 0 1) := by
  intro t ht
  rcases eq_or_ne t 0 with rfl | htne
  · have hval : divProfile (profileCoherentProfile f g) 0 = 0 := by rw [divProfile, if_pos rfl]
    rw [ContinuousWithinAt, hval]
    refine squeeze_zero' (g := fun x : ℝ => (2 * L * Real.exp (3 * L)) ^ 2 * x) ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact divProfile_profileCoherent_nonneg f g hx.1
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact divProfile_profileCoherent_le hf hg hx
    · have hid : Filter.Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Icc 0 1)) (nhds 0) :=
        (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
      have := hid.const_mul ((2 * L * Real.exp (3 * L)) ^ 2)
      simpa using this
  · have hcont : ContinuousWithinAt
        (fun x : ℝ => profileCoherentProfile f g x / x) (Set.Icc 0 1) t := by
      refine ContinuousWithinAt.div ?_ continuousWithinAt_id htne
      have hfx : ContinuousWithinAt f (Set.Icc 0 1) t := hf.cont t ht
      have hgx : ContinuousWithinAt g (Set.Icc 0 1) t := hg.cont t ht
      exact (((Real.continuous_exp.continuousAt.comp_continuousWithinAt hfx).sub
        (Real.continuous_exp.continuousAt.comp_continuousWithinAt hgx)).pow 2)
    refine hcont.congr ?_ ?_
    · intro x _
      rw [divProfile]
      by_cases hx : x = 0
      · simp [hx]
      · rw [if_neg hx]
    · rw [divProfile, if_neg htne]

/-! ## The profile parity digit and its critical limit -/

theorem bitHellingerAffinity_zero_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 < bitHellingerAffinity a b 0 := by
  rw [bitHellingerAffinity_zero_eq]
  have hnum : (0 : ℝ) < 1 + Real.sqrt (a * b) := by
    have := Real.sqrt_nonneg (a * b); linarith
  have hden : (0 : ℝ) < Real.sqrt ((1 + a) * (1 + b)) := by
    refine Real.sqrt_pos.mpr ?_
    nlinarith
  exact div_pos hnum hden

/-- The parity-digit affinity of the prime `n` between two prime-scale profiles. -/
def profileParityAffinity (f g : ℝ → ℝ) (N n : ℕ) : ℝ :=
  if n.Prime then bitHellingerAffinity (profileNome f N n) (profileNome g N n) 0 else 1

theorem profileParityAffinity_pos (f g : ℝ → ℝ) (N n : ℕ) : 0 < profileParityAffinity f g N n := by
  rw [profileParityAffinity]
  split_ifs with hp
  · exact bitHellingerAffinity_zero_pos (profileNome_pos hp.two_le).le
      (profileNome_pos hp.two_le).le
  · exact zero_lt_one

/-- The per-prime remainder of the profile parity expansion. -/
def profileRemainder (f g : ℝ → ℝ) (N n : ℕ) : ℝ :=
  if n.Prime then
    Real.log (bitHellingerAffinity (profileNome f N n) (profileNome g N n) 0)
      + profileCoherentProfile f g (Real.log n / Real.log N) / (n : ℝ) / 2
  else 0

theorem abs_profileRemainder_le {f g : ℝ → ℝ} {L : ℝ}
    (hf : IsScaleProfile f L) (hg : IsScaleProfile g L) {N n : ℕ}
    (hN : 2 ≤ N) (hNL : 16 * L ≤ Real.log N) (hnN : n ≤ N) :
    |profileRemainder f g N n| ≤ 8 * ((n : ℝ)) ^ (-(3 / 2 : ℝ)) := by
  rw [profileRemainder]
  split_ifs with hp
  · have hn : 2 ≤ n := hp.two_le
    have ha0 : 0 ≤ profileNome f N n := (profileNome_pos hn).le
    have hb0 : 0 ≤ profileNome g N n := (profileNome_pos hn).le
    have hkey := abs_log_bitHellingerAffinity_zero_add_le ha0 hb0
      (profileNome_le_three_quarters hf hn hnN hNL hN)
      (profileNome_le_three_quarters hg hn hnN hNL hN)
    have hdisp := sq_sqrt_profileNome_sub (f := f) (g := g) (N := N) hn
    rw [hdisp] at hkey
    have hprof : profileCoherentProfile f g (Real.log n / Real.log N)
        = (Real.exp (f (Real.log n / Real.log N))
            - Real.exp (g (Real.log n / Real.log N))) ^ 2 := rfl
    rw [hprof]
    refine le_trans hkey ?_
    have h1 := sq_profileNome_le hf hn hnN hNL hN
    have h2 := sq_profileNome_le hg hn hnN hNL hN
    linarith
  · have : (0 : ℝ) ≤ ((n : ℝ)) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    simpa using by linarith

theorem log_profileParityAffinity_eq (f g : ℝ → ℝ) (N n : ℕ) :
    Real.log (profileParityAffinity f g N n)
      = -((if n.Prime then
            profileCoherentProfile f g (Real.log n / Real.log N) / (n : ℝ) else 0) / 2)
        + profileRemainder f g N n := by
  by_cases hp : n.Prime
  · rw [profileParityAffinity, if_pos hp, profileRemainder, if_pos hp, if_pos hp]
    ring
  · rw [profileParityAffinity, if_neg hp, profileRemainder, if_neg hp, if_neg hp, Real.log_one]
    ring

theorem tendsto_profileValue_zero {f : ℝ → ℝ} {L : ℝ} (hf : IsScaleProfile f L) (n : ℕ)
    (hn : 2 ≤ n) : Tendsto (fun N : ℕ => f (Real.log n / Real.log N)) atTop (nhds 0) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hL := hf.slope_nonneg
  refine squeeze_zero_norm' (a := fun N : ℕ => L * (Real.log n / Real.log N)) ?_ ?_
  · filter_upwards [eventually_ge_atTop n, eventually_ge_atTop 2] with N hnN hN2
    have hmem := logRatio_mem hn hnN
    have := hf.slope _ hmem
    simpa [Real.norm_eq_abs] using this
  · have hdrift := tendsto_drift_zero (Real.log n)
    have := hdrift.const_mul L
    simpa using this

theorem tendsto_profileNome {f : ℝ → ℝ} {L : ℝ} (hf : IsScaleProfile f L) {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun N : ℕ => profileNome f N n) atTop (nhds ((n : ℝ))⁻¹) := by
  have hval := tendsto_profileValue_zero hf n hn
  have hexp : Tendsto (fun N : ℕ => Real.exp (2 * f (Real.log n / Real.log N))) atTop (nhds 1) := by
    have := (Real.continuous_exp.tendsto (2 * 0)).comp (hval.const_mul 2)
    simpa [Function.comp_def] using this
  have := (tendsto_const_nhds (x := ((n : ℝ))⁻¹) (f := atTop (α := ℕ))).mul hexp
  rw [mul_one] at this
  exact this.congr fun N => rfl

theorem tendsto_profileRemainder_zero {f g : ℝ → ℝ} {L : ℝ}
    (hf : IsScaleProfile f L) (hg : IsScaleProfile g L) (n : ℕ) :
    Tendsto (fun N : ℕ => profileRemainder f g N n) atTop (nhds 0) := by
  by_cases hp : n.Prime
  · have hn : 2 ≤ n := hp.two_le
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hinv0 : (0 : ℝ) ≤ ((n : ℝ))⁻¹ := by positivity
    have haff := tendsto_bitHellingerAffinity_zero_one hinv0
      (tendsto_profileNome hf hn) (tendsto_profileNome hg hn)
    have hlog : Tendsto
        (fun N : ℕ =>
          Real.log (bitHellingerAffinity (profileNome f N n) (profileNome g N n) 0))
        atTop (nhds 0) := by
      have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp haff
      simpa [Function.comp_def] using this
    have hchar : Tendsto
        (fun N : ℕ => profileCoherentProfile f g (Real.log n / Real.log N) / (n : ℝ) / 2)
        atTop (nhds 0) := by
      have h1 : Tendsto (fun N : ℕ => Real.exp (f (Real.log n / Real.log N))) atTop (nhds 1) := by
        have := (Real.continuous_exp.tendsto 0).comp (tendsto_profileValue_zero hf n hn)
        simpa [Function.comp_def] using this
      have h2 : Tendsto (fun N : ℕ => Real.exp (g (Real.log n / Real.log N))) atTop (nhds 1) := by
        have := (Real.continuous_exp.tendsto 0).comp (tendsto_profileValue_zero hg n hn)
        simpa [Function.comp_def] using this
      have := (((h1.sub h2).pow 2).div_const (n : ℝ)).div_const 2
      simpa [profileCoherentProfile] using this
    have := hlog.add hchar
    rw [add_zero] at this
    refine this.congr fun N => ?_
    rw [profileRemainder, if_pos hp]
  · simp only [profileRemainder, if_neg hp]
    exact tendsto_const_nhds

theorem tendsto_sum_profileRemainder {f g : ℝ → ℝ} {L : ℝ}
    (hf : IsScaleProfile f L) (hg : IsScaleProfile g L) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N, profileRemainder f g N n) atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine tendsto_finsetSum_Icc_zero summable_parityRemainderBound
    (fun n => by positivity) ?_ ?_
  · filter_upwards [eventually_ge_atTop 2, hlog.eventually_ge_atTop (16 * L)] with N hN hNL n hnN
    exact abs_profileRemainder_le hf hg hN hNL hnN
  · intro n
    exact tendsto_profileRemainder_zero hf hg n

/-- **`(13s)`: the prime-profile squarefree Fock limit.**  For arbitrary prime-scale profiles the
all-prime parity-digit affinity converges to the coherent kernel of the profile pair. -/
theorem tendsto_profileParityAffinity {f g : ℝ → ℝ} {L : ℝ}
    (hf : IsScaleProfile f L) (hg : IsScaleProfile g L) :
    Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc 0 N, profileParityAffinity f g N n)
      atTop
      (nhds (Real.exp (-((∫ t in (0 : ℝ)..1, divProfile (profileCoherentProfile f g) t) / 2)))) := by
  have hdisp := tendsto_sum_divProfile (profileCoherentProfile f g)
    (continuousOn_divProfile_profileCoherent hf hg)
  have hrem := tendsto_sum_profileRemainder hf hg
  have hsplit : ∀ N : ℕ,
      ∑ n ∈ Finset.Icc 0 N, Real.log (profileParityAffinity f g N n)
        = -((∑ n ∈ Finset.Icc 0 N,
              (if n.Prime then
                profileCoherentProfile f g (Real.log n / Real.log N) / (n : ℝ) else 0)) / 2)
          + ∑ n ∈ Finset.Icc 0 N, profileRemainder f g N n := by
    intro N
    rw [Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => log_profileParityAffinity_eq f g N n
  have hlim : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N, Real.log (profileParityAffinity f g N n))
      atTop
      (nhds (-((∫ t in (0 : ℝ)..1, divProfile (profileCoherentProfile f g) t) / 2))) := by
    have hcomb := ((hdisp.div_const 2).neg).add hrem
    rw [add_zero] at hcomb
    refine hcomb.congr fun N => (hsplit N).symm |>.trans ?_
    rfl
  exact tendsto_prod_Icc_of_tendsto_sum_log
    (Filter.Eventually.of_forall fun N n _ => profileParityAffinity_pos f g N n) hlim

/-! ## The radial line inside the profile field, and totality -/

theorem isScaleProfile_linear (u : ℝ) : IsScaleProfile (fun t => u * t) |u| := by
  refine ⟨(continuous_const.mul continuous_id).continuousOn, fun t ht => ?_⟩
  rw [abs_mul, abs_of_nonneg ht.1]

/-- The radial family is the linear line of the profile field. -/
theorem profileParityAffinity_linear (u v : ℝ) (N n : ℕ) :
    profileParityAffinity (fun t => u * t) (fun t => v * t) N n
      = parityDigitAffinity (u / Real.log N) (v / Real.log N) n := by
  rw [profileParityAffinity, parityDigitAffinity]
  split_ifs with hp
  · rw [profileNome_linear u N n hp.two_le, profileNome_linear v N n hp.two_le]
  · rfl

theorem profileCoherentProfile_linear (u v : ℝ) :
    profileCoherentProfile (fun t => u * t) (fun t => v * t) = coherentProfile u v := by
  funext t
  rw [profileCoherentProfile, coherentProfile]

/-- **`(13z)`: the profile field sweeps a neighbourhood of the origin in the prime-scale Hilbert
space.**  Every small multiple of a bounded probe is a profile vector, so the coherent field is
total. -/
theorem profileVector_log_one_add (φ : ℝ → ℝ) (ε : ℝ) {t : ℝ} (h : 0 < 1 + ε * φ t) :
    Real.exp (Real.log (1 + ε * φ t)) - 1 = ε * φ t := by
  rw [Real.exp_log h]
  ring

end

end RHTower
