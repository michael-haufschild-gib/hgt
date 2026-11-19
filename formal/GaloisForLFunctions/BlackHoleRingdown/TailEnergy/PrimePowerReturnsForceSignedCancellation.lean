import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.FixedStepContractionFalsification

/-!
# The return that the other scattering paths must cancel

In the Gram expansion of Gabet, Ferreira Da Costa and Lee
(arXiv:2611.18900, §4), discarding cross terms retains the individual
path intensities. At the modular cusp, the same prime-power path recurs
at arbitrarily late times with unchanged amplitude. After subtracting
the exact mean, the other paths must converge to its negative.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology Finset
namespace GaloisForLFunctions.BlackHoleRingdown.ReturnCancellation

/-- Response to a single unit-weight bounce at time zero. -/
def bounce (h : CompactPulse) (u : ℝ) : ℂ :=
  ∫ v in Ioi (0 : ℝ), h (u-v)*((bounceKernel v : ℝ) : ℂ)

/-- Individual summand in the physical field. -/
def path (h : CompactPulse) (c : ℕ) (t : ℝ) : ℂ :=
  (echoWeight c : ℂ) * bounce h (t-echoDelay c)

/-- Every compact pulse, including pulses with nonzero mean, has an exact
finite return expansion after the explicit growing term is restored. -/
theorem finite_return_sum (h : CompactPulse) {S B t : ℝ}
    (hs : ∀ s : ℝ, S < |s| → h s = 0) (ht : t ≤ B) :
    ∑ c ∈ Icc 1 (pathReturnCutoff (B+S)), path h c t =
      pulseReflected h t + meanCoefficient h * cexp ((t : ℂ)/2) := by
  rw [← h.pulseEcho_eq, pulseEcho]
  let F := Finset.Icc 1 (pathReturnCutoff (B+S))
  have hpt (w : ℝ) : h (t-w) * (echoKernel w : ℂ) =
      ∑ c ∈ F, h (t-w) * (echoTerm c w : ℂ) := by
    by_cases hw : w ≤ B+S
    · rw [echoKernel_eq_finset_sum_of_le hw, Complex.ofReal_sum, Finset.mul_sum]
    · have hh : S < |t-w| := by
        rw [abs_sub_comm]
        exact (by linarith : S < w-t).trans_le (le_abs_self _)
      simp [hs _ hh]
  simp_rw [hpt]
  rw [integral_finsetSum F fun c _ => integrable_pulse_mul_echoTerm h c t]
  exact sum_congr rfl fun c _ => (integral_pulse_mul_echoTerm_eq_bounce h c t).symm

/-- A cutoff containing the selected denominator even when the sampled
bounce time is negative. -/
def denominators (S u : ℝ) (c : ℕ) : Finset ℕ :=
  Icc 1 (pathReturnCutoff (echoDelay c+max u 0+S))

private theorem mem_denominators {c : ℕ} (hc : 0 < c) (u : ℝ) {S : ℝ} (hS : 0 ≤ S) :
    c ∈ denominators S u c := by
  refine mem_Icc.mpr ⟨hc, ?_⟩
  have hc' : (0 : ℝ) < c := Nat.cast_pos.mpr hc
  have he : (c : ℝ) ≤ Real.exp ((echoDelay c+max u 0+S)/2) := by
    calc (c : ℝ) = Real.exp (Real.log c) := (Real.exp_log hc').symm
         _ ≤ _ := Real.exp_le_exp.mpr (by unfold echoDelay; linarith only [le_max_right u 0,hS])
  exact Nat.cast_le.mp (he.trans (Nat.le_ceil _))

/-- All other paths at the selected arrival, after removing the mean. -/
def others (h : CompactPulse) (S u : ℝ) (c : ℕ) : ℂ :=
  (∑ m ∈ (denominators S u c).erase c, path h m (echoDelay c+u)) -
    meanCoefficient h * cexp (((echoDelay c+u : ℝ) : ℂ)/2)

/-- Exact cancellation error, before taking a limit or bounding the field. -/
theorem erase_one_return (h : CompactPulse) {S : ℝ} (hS : 0 ≤ S)
    (hs : ∀ s : ℝ, S < |s| → h s = 0) (u : ℝ) {c : ℕ} (hc : 0 < c) :
    others h S u c + (echoWeight c : ℂ)*bounce h u = pulseReflected h (echoDelay c+u) := by
  have he := finite_return_sum h hs (by linarith only [le_max_left u 0] :
    echoDelay c+u ≤ echoDelay c+max u 0)
  change (∑ m ∈ denominators S u c, path h m (echoDelay c+u)) = _ at he
  rw [← sum_erase_add _ _ (mem_denominators hc u hS)] at he
  have hpath : path h c (echoDelay c+u) = (echoWeight c : ℂ)*bounce h u := by
    rw [path, add_sub_cancel_left]
  rw [hpath] at he
  unfold others
  linear_combination he

/-- Each prime furnishes an infinite geometric sequence of tests. At every
known decay rate the remaining signed paths cancel the *same* wave with
geometrically decreasing error in the prime-power index. -/
theorem prime_power_cancellation_rate (h : CompactPulse) {σ : ℝ} (hσ : 0 < σ)
    (hσ' : σ < 3001/48000) {S : ℝ} (hS : 0 ≤ S)
    (hs : ∀ s : ℝ, S < |s| → h s = 0) {p : ℕ} (hp : p.Prime) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ) (k : ℕ), 1 ≤ k → 0 ≤ echoDelay (p^k)+u →
      ‖others h S u (p^k) + ((1-1/(p : ℝ) : ℝ) : ℂ)*bounce h u‖ ≤
        C * Real.exp (-σ*u) * (Real.exp (-2*σ*Real.log p))^k := by
  obtain ⟨C,hC,hfield,_⟩ := (unconditional_cusp_escape_sub_seven_eighths hσ hσ' h).2
  refine ⟨C,hC,fun u k hk ht => ?_⟩
  obtain ⟨hd,hw⟩ := echoDelay_and_weight_prime_pow hp hk
  rw [← hw, erase_one_return h hS hs u (pow_pos hp.pos _)]
  refine (hfield _ ht).trans_eq ?_
  rw [hd, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- A nonzero mean-zero pulse has a nonzero single-bounce waveform.
Hence the forced cancellation is nontrivial for every such pulse. -/
theorem exists_nonzero_bounce (h : CompactPulse) (hm : meanCoefficient h = 0)
    (hne : ∃ s : ℝ, h s ≠ 0) : ∃ u : ℝ, bounce h u ≠ 0 := by
  by_contra! hall
  obtain ⟨S,_,hs⟩ := h.exists_support_bound
  have hz (t : ℝ) : pulseReflected h t = 0 := by
    have he := finite_return_sum (B := t) h hs le_rfl
    simpa [path, hall, hm] using he.symm
  have he := tailEnergy_pos h hne 0
  simp [tailEnergy, hz] at he

/-- Along every prime-power tower the remaining paths converge to the
negative of the individual path. The same base time works for every prime. -/
theorem prime_power_cancellation_limit (h : CompactPulse) {S : ℝ} (hS : 0 ≤ S)
    (hs : ∀ s : ℝ, S < |s| → h s = 0) {p : ℕ} (hp : p.Prime) (u : ℝ) :
    Tendsto (fun k : ℕ => others h S u (p^k)) atTop
      (𝓝 (-(((1-1/(p : ℝ) : ℝ) : ℂ)*bounce h u))) := by
  let σ : ℝ := 1/32
  have hσ : 0 < σ := by norm_num [σ]
  obtain ⟨C,_,hC⟩ := prime_power_cancellation_rate h hσ (by norm_num [σ]) hS hs hp
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  let a := Real.exp (-2*σ*Real.log p)
  have ha : a < 1 := Real.exp_lt_one_iff.mpr (by nlinarith only [mul_pos hσ hlog])
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le ha
  have htime : Tendsto (fun k : ℕ => (k : ℝ)*(2*Real.log p)+u) atTop atTop :=
    tendsto_atTop_add_const_right _ _ ((tendsto_mul_const_atTop_of_pos (by positivity)).mpr
      tendsto_natCast_atTop_atTop)
  have hb : Tendsto (fun k : ℕ => C*Real.exp (-σ*u)*a^k) atTop (𝓝 0) := by
    simpa using hpow.const_mul (C*Real.exp (-σ*u))
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hb.eventually_lt_const hε, eventually_ge_atTop 1,
    htime.eventually_ge_atTop 0] with k hk hk1 hlate
  have ht : 0 ≤ echoDelay (p^k)+u := by
    rw [(echoDelay_and_weight_prime_pow hp hk1).1]
    linarith only [hlate]
  rw [dist_eq_norm, sub_neg_eq_add]
  exact (hC u k hk1 ht).trans_lt hk

private theorem bounce_before_support (h : CompactPulse) {S : ℝ} (hs : ∀ s : ℝ, S < |s| → h s = 0)
    {u : ℝ} (hu : u ≤ -S) : bounce h u = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro v hv
  have hl : S < |u-v| := by
    rw [abs_sub_comm]
    exact (by linarith only [hu, (show 0 < v from hv)] : S < v-u).trans_le (le_abs_self _)
  simp only [hs _ hl, zero_mul]

private theorem path_finite (h : CompactPulse) {S : ℝ} (hs : ∀ s : ℝ, S < |s| → h s = 0)
    (t : ℝ) (c : ℕ) (hc : c ∉ Finset.Icc 1 (pathReturnCutoff (t+S))) : path h c t = 0 := by
  rcases Nat.eq_zero_or_pos c with rfl | hpos
  · simp [path,echoWeight]
  have hc' : pathReturnCutoff (t+S) < c := lt_of_not_ge (fun hle => hc (mem_Icc.mpr ⟨hpos,hle⟩))
  have he := (Nat.le_ceil (Real.exp ((t+S)/2))).trans (Nat.cast_le.mpr hc'.le)
  have hl := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hpos)).mpr he
  rw [path, bounce_before_support h hs (by unfold echoDelay; linarith only [hl]), mul_zero]

private theorem path_hasSum (h : CompactPulse) (t : ℝ) :
    HasSum (fun c => path h c t) (pulseEcho h t) := by
  obtain ⟨S,_,hs⟩ := h.exists_support_bound
  have he := hasSum_sum_of_ne_finset_zero (path_finite h hs t)
  rwa [finite_return_sum h hs (le_refl t), ← h.pulseEcho_eq] at he

/-- The part of the echo carried by denominators divisible by q. -/
def multipleEcho (h : CompactPulse) (q : ℕ) (t : ℝ) : ℂ :=
  ∑' a : ℕ, path h (q*a) t

private theorem echoWeight_prime_mul {p : ℕ} (hp : p.Prime) (a : ℕ) :
    echoWeight (p*a) = if p ∣ a then echoWeight a else (1-1/(p:ℝ))*echoWeight a := by
  have hp0 := (Nat.cast_pos.mpr hp.pos : (0:ℝ) < p).ne'
  unfold echoWeight
  rw [Nat.cast_mul]
  split_ifs with hd
  · rw [Nat.totient_mul_of_prime_of_dvd hp hd, Nat.cast_mul, mul_div_mul_left _ _ hp0]
  · rw [Nat.totient_mul_of_prime_of_not_dvd hp hd, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one]
    by_cases ha : a = 0
    · subst a; simp
    field_simp [hp0, (by exact_mod_cast ha : (a:ℝ) ≠ 0)] <;> ring

private theorem echoDelay_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    echoDelay (a*b) = echoDelay a+echoDelay b := by
  rw [echoDelay, Nat.cast_mul, Real.log_mul (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')]
  unfold echoDelay
  ring

private theorem path_prime_tower (h : CompactPulse) {p : ℕ} (hp : p.Prime) (k a : ℕ) (u : ℝ) :
    path h (p^(k+1)*a) (echoDelay (p^(k+1))+u) =
      (echoWeight (p*a) : ℂ)*bounce h (u-echoDelay a) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [path,echoWeight]
  have hw : echoWeight (p^(k+1)*a) = echoWeight (p*a) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_assoc, echoWeight_prime_mul hp, if_pos, ih]
      exact dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
  rw [path, hw, echoDelay_mul (pow_pos hp.pos _) ha]
  congr 2
  ring

/-- At the corresponding translated time the entire prime-power sector
repeats exactly, for every compact input and every positive power. -/
theorem repeated_prime_sector (h : CompactPulse) {p : ℕ} (hp : p.Prime) (k : ℕ) (u : ℝ) :
    multipleEcho h (p^(k+1)) (echoDelay (p^(k+1))+u) = multipleEcho h p (echoDelay p+u) := by
  unfold multipleEcho
  apply tsum_congr
  intro a
  exact (path_prime_tower h hp k a u).trans (by simpa using (path_prime_tower h hp 0 a u).symm)

private theorem tsum_on_multiples (h : CompactPulse) {q : ℕ} (hq : 0 < q) (t : ℝ) :
    (∑' a, if q ∣ a then path h a t else 0) = multipleEcho h q t := by
  let f := fun a : ℕ => if q ∣ a then path h a t else 0
  have hi : Function.Injective (fun a : ℕ => q*a) := fun _ _ he => Nat.eq_of_mul_eq_mul_left hq he
  have hs : Function.support f ⊆ Set.range (fun a : ℕ => q*a) := by
    intro a ha
    by_contra hn
    have hnd : ¬q ∣ a := fun ⟨d,hd⟩ => hn ⟨d,hd.symm⟩
    exact ha (if_neg hnd)
  simpa only [f, if_pos (dvd_mul_right q _), multipleEcho] using (hi.tsum_eq hs).symm

/-- The sector at its first prime delay satisfies a scalar delay recurrence.
The forcing is the full physical echo, including the mean. -/
theorem prime_sector_delay (h : CompactPulse) {p : ℕ} (hp : p.Prime) (u : ℝ) :
    multipleEcho h p (echoDelay p+u) =
      (1-1/(p:ℂ))*pulseEcho h u + (1/(p:ℂ))*multipleEcho h p u := by
  let A := fun a : ℕ => path h a u
  let B := fun a : ℕ => if p ∣ a then A a else 0
  have hA : Summable A := (path_hasSum h u).summable
  have hB : Summable B := by
    obtain ⟨S,_,hs⟩ := h.exists_support_bound
    exact summable_of_ne_finset_zero (s := Finset.Icc 1 (pathReturnCutoff (u+S)))
      (fun a ha => by simp [B,A,path_finite h hs u a ha])
  have term (a : ℕ) : path h (p*a) (echoDelay p+u) =
      (1-1/(p:ℂ))*A a + (1/(p:ℂ))*B a := by
    rw [show path h (p*a) (echoDelay p+u) = _ from
      (by simpa using path_prime_tower h hp 0 a u :
        path h (p*a) (echoDelay p+u) = (echoWeight (p*a):ℂ)*bounce h (u-echoDelay a)),
      echoWeight_prime_mul hp]
    by_cases hd : p ∣ a <;> simp only [B,A,path, if_pos, if_neg, hd, ↓reduceIte,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast] <;> ring
  conv_lhs => rw [multipleEcho]; simp_rw [term]
  rw [(hA.mul_left _).tsum_add (hB.mul_left _), tsum_mul_left, tsum_mul_left,
    (path_hasSum h u).tsum_eq, tsum_on_multiples h hp.pos u]

/-- Subtracting the exact prime-sector mean gives the same scalar recurrence
forced by the decaying reflected field. The mean weight is p/(p+1). -/
def centeredPrimeSector (h : CompactPulse) (p : ℕ) (u : ℝ) : ℂ :=
  multipleEcho h p (echoDelay p+u) -
    ((p:ℂ)/(p+1))*meanCoefficient h*cexp ((u:ℂ)/2)

theorem centered_sector_delay (h : CompactPulse) {p : ℕ} (hp : p.Prime) (u : ℝ) :
    centeredPrimeSector h p u = (1-1/(p:ℂ))*pulseReflected h u +
      (1/(p:ℂ))*centeredPrimeSector h p (u-echoDelay p) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℂ)+1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero p)
  have hshift : cexp (((u-echoDelay p : ℝ):ℂ)/2) = cexp ((u:ℂ)/2)/(p:ℂ) := by
    rw [echoDelay, Complex.ofReal_sub, sub_div, Complex.exp_sub]
    congr 1
    rw [Complex.ofReal_mul, Complex.ofReal_ofNat, show (2:ℂ)*↑(Real.log p)/2 = ↑(Real.log p) by ring,
      ← Complex.ofReal_exp, Real.exp_log (Nat.cast_pos.mpr hp.pos), Complex.ofReal_natCast]
  unfold centeredPrimeSector
  rw [prime_sector_delay h hp u, h.pulseEcho_eq, show echoDelay p+(u-echoDelay p)=u by ring, hshift]
  field_simp [hp0,hp1] <;> ring

/-- A bounded exponential envelope on the physical time axis. -/
def weightedBound (σ : ℝ) (F : ℝ → ℂ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, ‖(Real.exp (σ*u):ℂ)*F u‖ ≤ C

private theorem stable_delay {Y F : ℝ → ℂ} {a : ℂ} (ha : a ≠ 0) {b d : ℝ}
    (hb : 0 ≤ b) (hb1 : b < 1) (hd : 0 < d)
    (he : ∀ u, Y u = a*F u+(b:ℂ)*Y (u-d))
    {s M : ℝ} (hbefore : ∀ u ≤ s, ‖Y u‖ ≤ M) :
    (∃ C : ℝ, ∀ u, ‖Y u‖ ≤ C) ↔ ∃ C : ℝ, ∀ u, ‖F u‖ ≤ C := by
  have hbn : ‖(b:ℂ)‖=b := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb]
  constructor
  · rintro ⟨C,hC⟩
    refine ⟨(C+b*C)/‖a‖, fun u => (le_div_iff₀ (norm_pos_iff.mpr ha)).mpr ?_⟩
    calc ‖F u‖*‖a‖ = ‖Y u-(b:ℂ)*Y (u-d)‖ := by rw [he u,add_sub_cancel_right,norm_mul,mul_comm]
         _ ≤ ‖Y u‖+‖(b:ℂ)*Y (u-d)‖ := norm_sub_le _ _
         _ ≤ _ := by rw [norm_mul,hbn]; exact add_le_add (hC _) (mul_le_mul_of_nonneg_left (hC _) hb)
  · rintro ⟨C,hC⟩
    let L := max M (‖a‖*C/(1-b))
    have hL : ‖a‖*C ≤ L*(1-b) := (div_le_iff₀ (sub_pos.mpr hb1)).mp (le_max_right _ _)
    have stretch (n : ℕ) : ∀ u ≤ s+n*d, ‖Y u‖ ≤ L := by
      induction n with
      | zero =>
        intro u hu
        exact (hbefore _ (by simpa using hu)).trans (le_max_left _ _)
      | succ n ih =>
        intro u hu
        have hback : u-d ≤ s+n*d := by push_cast at hu; linarith only [hu]
        rw [he u]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul,norm_mul,hbn]
        have hF := mul_le_mul_of_nonneg_left (hC u) (norm_nonneg a)
        have hY := mul_le_mul_of_nonneg_left (ih _ hback) hb
        linarith only [hL,hF,hY]
    refine ⟨L,fun u => ?_⟩
    obtain ⟨n,hn⟩ := exists_nat_ge ((u-s)/d)
    exact stretch n u (by linarith only [(div_le_iff₀ hd).mp hn])

private theorem sector_before (h : CompactPulse) {p : ℕ} (hp : p.Prime)
    {S : ℝ} (hs : ∀ s : ℝ, S < |s| → h s = 0) {u : ℝ} (hu : u ≤ -S) :
    centeredPrimeSector h p u = -(((p:ℂ)/(p+1))*meanCoefficient h*cexp ((u:ℂ)/2)) := by
  have hz (a : ℕ) : path h (p*a) (echoDelay p+u) = 0 := by
    have he := path_prime_tower h hp 0 a u
    simp only [zero_add,pow_one] at he
    rw [he,bounce_before_support h hs (by linarith only [hu,echoDelay_nonneg a]),mul_zero]
  simp [centeredPrimeSector,multipleEcho,hz]

/-- Every prime sector has precisely the same exponential decay thresholds
as the reflected field below the half-power. The return factor becomes
exp(σ·2 log p)/p after applying the exponential weight. -/
theorem prime_sector_weightedBound_iff (h : CompactPulse) {p : ℕ} (hp : p.Prime)
    {σ : ℝ} (hσ : 0 ≤ σ) (hhalf : σ < 1/2) :
    weightedBound σ (centeredPrimeSector h p) ↔ weightedBound σ (pulseReflected h) := by
  let d := echoDelay p
  let b := Real.exp (σ*d)/(p:ℝ)
  let a := 1-1/(p:ℂ)
  let Y := fun u : ℝ => (Real.exp (σ*u):ℂ)*centeredPrimeSector h p u
  let F := fun u : ℝ => (Real.exp (σ*u):ℂ)*pulseReflected h u
  have hp0 : 0 < (p:ℝ) := Nat.cast_pos.mpr hp.pos
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hlog := Real.log_pos hp1
  have hd : 0 < d := mul_pos (by norm_num) hlog
  have hb : 0 ≤ b := div_nonneg (Real.exp_pos _).le hp0.le
  have hb1 : b < 1 := by
    apply (div_lt_one hp0).mpr
    rw [← Real.exp_log hp0]
    apply Real.exp_lt_exp.mpr
    change σ*(2*Real.log p) < _
    nlinarith only [mul_pos (sub_pos.mpr hhalf) hlog]
  have ha : a ≠ 0 := by
    have hr : 0 < 1-1/(p:ℝ) := sub_pos.mpr ((div_lt_one hp0).mpr hp1)
    exact_mod_cast hr.ne'
  have hrec (u : ℝ) : Y u = a*F u+(b:ℂ)*Y (u-d) := by
    have hE : (Real.exp (σ*d):ℂ)*(Real.exp (σ*(u-d)):ℂ)=(Real.exp (σ*u):ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add, show σ*d+σ*(u-d)=σ*u by ring]
    dsimp only [Y,F,a,b]
    rw [centered_sector_delay h hp u,Complex.ofReal_div,Complex.ofReal_natCast]
    change _ = _ + _ * (_ * centeredPrimeSector h p (u-echoDelay p))
    linear_combination -(1/(p:ℂ))*centeredPrimeSector h p (u-d)*hE
  obtain ⟨S,hS,hs⟩ := h.exists_support_bound
  have hbefore (u : ℝ) (hu : u ≤ -S) : ‖Y u‖ ≤ ‖((p:ℂ)/(p+1))*meanCoefficient h‖ := by
    have hu0 : u ≤ 0 := by linarith only [hu,hS]
    have he₁ : Real.exp (σ*u) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hσ hu0)
    have he₂ : Real.exp (u/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    change ‖(Real.exp (σ*u):ℂ)*centeredPrimeSector h p u‖ ≤ _
    rw [sector_before h hp hs hu,norm_mul,norm_neg,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Complex.norm_exp,
      Complex.div_ofNat_re,Complex.ofReal_re]
    exact (mul_le_of_le_one_left (by positivity) he₁).trans
      (mul_le_of_le_one_right (norm_nonneg _) he₂)
  exact stable_delay ha hb hb1 hd hrec hbefore

private theorem weighted_estimate (σ u C : ℝ) (z : ℂ) :
    ‖(Real.exp (σ*u):ℂ)*z‖ ≤ C ↔ ‖z‖ ≤ C*Real.exp (-σ*u) := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
    mul_comm (Real.exp (σ*u)),← le_div_iff₀ (Real.exp_pos _),div_eq_mul_inv,
    ← Real.exp_neg,neg_mul]

private theorem reflected_uniform (h : CompactPulse) (u : ℝ) :
    ‖pulseReflected h u‖ ≤ ∫ ξ : ℝ, ‖pulseAmplitude h (ξ:ℂ)‖ := by
  unfold pulseReflected
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  simp only [norm_mul,norm_scatteringPhase_line,norm_exp_I_mul,mul_one]

private theorem reflected_weighted_iff (h : CompactPulse) {σ : ℝ} (hσ : 0 ≤ σ) :
    weightedBound σ (pulseReflected h) ↔
      ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → ‖pulseReflected h u‖ ≤ C*Real.exp (-σ*u) := by
  constructor
  · rintro ⟨C,hC⟩
    exact ⟨C,fun u _ => (weighted_estimate _ _ _ _).mp (hC u)⟩
  · rintro ⟨C,hC⟩
    let M := ∫ ξ : ℝ, ‖pulseAmplitude h (ξ:ℂ)‖
    refine ⟨max C M,fun u => ?_⟩
    rcases le_or_gt 0 u with hu | hu
    · exact ((weighted_estimate _ _ _ _).mpr (hC _ hu)).trans (le_max_left _ _)
    · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      have hsmall := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hσ hu.le)
      exact ((mul_le_of_le_one_left (norm_nonneg _) hsmall).trans (reflected_uniform h u)).trans
        (le_max_right _ _)

/-- Looking at denominators divisible by a single fixed prime still
recovers the entire zero-free strip. The target rate is approached from
below to allow poles at its endpoint. -/
theorem strip_iff_one_prime_sector {δ : ℝ} (hδ₀ : 0 < δ) (hδ : δ ≤ 1/4)
    {p : ℕ} (hp : p.Prime) :
    (∀ ρ : ℂ, riemannZeta ρ=0 → 0 < ρ.re → ρ.re ≤ 1-2*δ) ↔
      ∀ σ : ℝ, 0 < σ → σ < δ → ∀ h : CompactPulse, weightedBound σ (centeredPrimeSector h p) := by
  constructor
  · intro hz σ hσ hσδ h
    obtain ⟨C,_,he,_⟩ := pulseReflected_decay_of_zeroFree hδ hσ hσδ hz h
    exact (prime_sector_weightedBound_iff h hp hσ.le (by linarith)).mpr
      ((reflected_weighted_iff h hσ.le).mpr ⟨C,he⟩)
  · intro hsector ρ hρ hρ0
    by_contra! hbad
    let σ := (δ+max 0 ((1-ρ.re)/2))/2
    have hlt : max 0 ((1-ρ.re)/2) < δ := max_lt hδ₀ (by linarith only [hbad])
    have hσ : 0 < σ := by dsimp [σ]; linarith only [hδ₀,le_max_left 0 ((1-ρ.re)/2)]
    have hσδ : σ < δ := by dsimp [σ]; linarith only [hlt]
    have hd (h : CompactPulse) := (reflected_weighted_iff h hσ.le).mp
      ((prime_sector_weightedBound_iff h hp hσ.le (by linarith)).mp (hsector σ hσ hσδ h))
    have he := re_le_of_pulseReflected_decay hσ (hσδ.le.trans hδ) hd hρ hρ0
    dsimp only [σ] at he
    linarith only [he,hlt,le_max_right 0 ((1-ρ.re)/2)]

/-- For any chosen prime the centered sector alone detects RH at the
quarter-rate threshold, on all compact pulses. -/
theorem rh_iff_one_prime_sector {p : ℕ} (hp : p.Prime) :
    RiemannHypothesis ↔ ∀ σ : ℝ, 0 < σ → σ < 1/4 →
      ∀ h : CompactPulse, weightedBound σ (centeredPrimeSector h p) := by
  have he := zeroFreeStrip_tailEnergy_equivalences (δ := 1/4) (by norm_num) le_rfl
  exact (RingdownRate.riemannHypothesis_iff_pulse_ringdown.trans he.1.symm).trans
    (strip_iff_one_prime_sector (by norm_num) le_rfl hp)

#print axioms strip_iff_one_prime_sector
#print axioms rh_iff_one_prime_sector
#print axioms prime_sector_weightedBound_iff
#print axioms repeated_prime_sector
#print axioms prime_sector_delay
#print axioms centered_sector_delay
#print axioms finite_return_sum
#print axioms erase_one_return
#print axioms prime_power_cancellation_rate
#print axioms exists_nonzero_bounce
#print axioms prime_power_cancellation_limit
end GaloisForLFunctions.BlackHoleRingdown.ReturnCancellation
