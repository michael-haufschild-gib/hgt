import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.SchurCapacity

/-!
# Escort transport, the logarithmic-odds clock, and phase dilation

The ramification power `r` acts on a Bernoulli occupation probability by the escort map

`R_r q = q^r / (q^r + (1-q)^r)`,

which multiplies the odds `o(q) = q/(1-q)` by the exponent: `o(R_r q) = o(q)^r`.  Hence
`R_1 = id`, `R_s R_r = R_{sr}`, and the signed log-odds clock
`L_τ q = -(1/τ) log o(q)` conjugates escort transport to scalar dilation:

`L_τ (R_r q) = r · L_τ q`.

Exponentiating gives the phase time-dilation square `Ph_t(L_τ(R_r q)) = Ph_{rt}(L_τ q)`.  The
comparison is flat: `L_τ` is a bijection of `(0,1)` onto `ℝ`.

Information loss occurs only after scalarisation: the Bernoulli variance, hence the whole
parity--energy Schur capacity, is invariant under `q ↦ 1 - q`, while the clock changes sign.
-/

namespace HTGeometry.ConstraintFrameRelativity

open Finset

/-! ## Odds coordinates -/

/-- The odds of a probability. -/
noncomputable def probToOdds (q : ℝ) : ℝ := q / (1 - q)

/-- The probability of given odds. -/
noncomputable def oddsToProb (o : ℝ) : ℝ := o / (1 + o)

theorem probToOdds_pos {q : ℝ} (h0 : 0 < q) (h1 : q < 1) : 0 < probToOdds q := by
  rw [probToOdds]
  exact div_pos h0 (by linarith)

theorem oddsToProb_mem {o : ℝ} (ho : 0 < o) : 0 < oddsToProb o ∧ oddsToProb o < 1 := by
  have hd : (0 : ℝ) < 1 + o := by linarith
  refine ⟨div_pos ho hd, ?_⟩
  rw [oddsToProb, div_lt_one hd]
  linarith

theorem oddsToProb_probToOdds {q : ℝ} (h1 : q < 1) : oddsToProb (probToOdds q) = q := by
  have hd : (0 : ℝ) ≠ 1 - q := by linarith
  rw [oddsToProb, probToOdds]
  field_simp
  ring

theorem probToOdds_oddsToProb {o : ℝ} (ho : 0 < o) : probToOdds (oddsToProb o) = o := by
  have hd : (0 : ℝ) < 1 + o := by linarith
  rw [probToOdds, oddsToProb]
  field_simp
  ring

/-! ## The escort map -/

/-- The escort transform of a probability. -/
noncomputable def escortMap (r : ℕ) (q : ℝ) : ℝ := q ^ r / (q ^ r + (1 - q) ^ r)

theorem escortMap_eq_oddsToProb {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (r : ℕ) :
    escortMap r q = oddsToProb ((probToOdds q) ^ r) := by
  have hq : (0 : ℝ) < 1 - q := by linarith
  have hqr : ((1 - q) ^ r) ≠ 0 := (pow_pos hq r).ne'
  have hden : (q ^ r + (1 - q) ^ r) ≠ 0 := by
    have : (0 : ℝ) < q ^ r + (1 - q) ^ r := add_pos (pow_pos h0 r) (pow_pos hq r)
    exact this.ne'
  rw [escortMap, oddsToProb, probToOdds, div_pow]
  field_simp
  ring

theorem escortMap_mem {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (r : ℕ) :
    0 < escortMap r q ∧ escortMap r q < 1 := by
  rw [escortMap_eq_oddsToProb h0 h1]
  exact oddsToProb_mem (pow_pos (probToOdds_pos h0 h1) r)

/-- **The escort map multiplies odds exponents.** -/
theorem probToOdds_escortMap {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (r : ℕ) :
    probToOdds (escortMap r q) = (probToOdds q) ^ r := by
  rw [escortMap_eq_oddsToProb h0 h1]
  exact probToOdds_oddsToProb (pow_pos (probToOdds_pos h0 h1) r)

/-- **The escort semigroup is the identity at exponent one.** -/
theorem escortMap_one {q : ℝ} (h0 : 0 < q) (h1 : q < 1) : escortMap 1 q = q := by
  rw [escortMap_eq_oddsToProb h0 h1, pow_one, oddsToProb_probToOdds h1]

/-- **Strict multiplicative coherence of escort transport.** -/
theorem escortMap_comp {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (r s : ℕ) :
    escortMap s (escortMap r q) = escortMap (s * r) q := by
  obtain ⟨hp0, hp1⟩ := escortMap_mem h0 h1 r
  rw [escortMap_eq_oddsToProb hp0 hp1, probToOdds_escortMap h0 h1,
    escortMap_eq_oddsToProb h0 h1, ← pow_mul, mul_comm r s]

/-! ## The signed log-odds clock -/

/-- The signed log-odds clock. -/
noncomputable def logitClock (τ q : ℝ) : ℝ := -(1 / τ) * Real.log (probToOdds q)

/-- The inverse of the log-odds clock. -/
noncomputable def logitInv (τ x : ℝ) : ℝ :=
  Real.exp (-τ * x) / (1 + Real.exp (-τ * x))

theorem logitInv_eq (τ x : ℝ) : logitInv τ x = oddsToProb (Real.exp (-τ * x)) := rfl

theorem logitInv_mem (τ x : ℝ) : 0 < logitInv τ x ∧ logitInv τ x < 1 :=
  oddsToProb_mem (Real.exp_pos _)

theorem logitInv_logitClock {τ : ℝ} (hτ : τ ≠ 0) {q : ℝ} (h0 : 0 < q) (h1 : q < 1) :
    logitInv τ (logitClock τ q) = q := by
  have hodds := probToOdds_pos h0 h1
  rw [logitInv_eq, logitClock]
  have : -τ * (-(1 / τ) * Real.log (probToOdds q)) = Real.log (probToOdds q) := by
    field_simp
  rw [this, Real.exp_log hodds, oddsToProb_probToOdds h1]

theorem logitClock_logitInv {τ : ℝ} (hτ : τ ≠ 0) (x : ℝ) :
    logitClock τ (logitInv τ x) = x := by
  rw [logitClock, logitInv_eq, probToOdds_oddsToProb (Real.exp_pos _), Real.log_exp]
  field_simp

/-- **Escort transport is scalar dilation in the clock coordinate.** -/
theorem logitClock_escortMap {τ : ℝ} {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (r : ℕ) :
    logitClock τ (escortMap r q) = r * logitClock τ q := by
  rw [logitClock, logitClock, probToOdds_escortMap h0 h1,
    Real.log_pow]
  ring

/-- **The reflected state has the opposite clock.** -/
theorem logitClock_one_sub {τ : ℝ} {q : ℝ} (h1 : q < 1) :
    logitClock τ (1 - q) = -logitClock τ q := by
  have hq : (0 : ℝ) < 1 - q := by linarith
  have hodds : probToOdds (1 - q) = (probToOdds q)⁻¹ := by
    rw [probToOdds, probToOdds, inv_div, show (1 : ℝ) - (1 - q) = q by ring]
  rw [logitClock, logitClock, hodds, Real.log_inv]
  ring

/-! ## Phase transport -/

/-- The diagonal phase observer. -/
noncomputable def phaseObs (t x : ℝ) : ℂ := Complex.exp (-(t * x) * Complex.I)

/-- **The phase time-dilation square.** -/
theorem phaseObs_dilation (t x : ℝ) (r : ℕ) :
    phaseObs t ((r : ℝ) * x) = phaseObs ((r : ℝ) * t) x := by
  rw [phaseObs, phaseObs]
  congr 2
  push_cast
  ring

/-- **The escorted phase history is the reparametrised history.** -/
theorem phaseObs_logitClock_escortMap {τ : ℝ} {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (r : ℕ)
    (t : ℝ) :
    phaseObs t (logitClock τ (escortMap r q)) = phaseObs ((r : ℝ) * t) (logitClock τ q) := by
  rw [logitClock_escortMap h0 h1, phaseObs_dilation]

/-! ## The literal shell section -/

/-- The Gibbs occupation of a prime at shell depth `m`. -/
noncomputable def shellOcc (p : ℕ) (m : ℕ) (τ : ℝ) : ℝ :=
  oddsToProb ((p : ℝ) ^ (-(m : ℝ) * τ))

theorem shellOcc_odds {p m : ℕ} (hp : 0 < (p : ℝ)) (τ : ℝ) :
    probToOdds (shellOcc p m τ) = (p : ℝ) ^ (-(m : ℝ) * τ) :=
  probToOdds_oddsToProb (Real.rpow_pos_of_pos hp _)

theorem shellOcc_mem {p m : ℕ} (hp : 0 < (p : ℝ)) (τ : ℝ) :
    0 < shellOcc p m τ ∧ shellOcc p m τ < 1 :=
  oddsToProb_mem (Real.rpow_pos_of_pos hp _)

/-- **Source power naturality.**  Escort transport realises the shell power event. -/
theorem escortMap_shellOcc {p : ℕ} (hp : 0 < (p : ℝ)) (m r : ℕ) (τ : ℝ) :
    escortMap r (shellOcc p m τ) = shellOcc p (r * m) τ := by
  obtain ⟨h0, h1⟩ := shellOcc_mem hp (m := m) τ
  rw [escortMap_eq_oddsToProb h0 h1, shellOcc_odds hp, shellOcc, ← Real.rpow_natCast _ r,
    ← Real.rpow_mul hp.le]
  congr 1
  push_cast
  ring

/-- **The literal prime clock.** -/
theorem logitClock_shellOcc {p : ℕ} (hp : 0 < (p : ℝ)) (m : ℕ) {τ : ℝ} (hτ : τ ≠ 0) :
    logitClock τ (shellOcc p m τ) = (m : ℝ) * Real.log p := by
  rw [logitClock, shellOcc_odds hp, Real.log_rpow hp]
  field_simp


/-! ## Scalar capacity does not inherit escort transport -/

/-- The Bernoulli variance of a probability. -/
noncomputable def bernVar (q : ℝ) : ℝ := q * (1 - q)

/-- **The second escort acts on the variance by `w ↦ w²/(1-2w)²`.** -/
theorem bernVar_escortMap_two {q : ℝ} (h0 : 0 < q) (h1 : q < 1) :
    bernVar (escortMap 2 q) = (bernVar q) ^ 2 / (1 - 2 * bernVar q) ^ 2 := by
  have hq : (0 : ℝ) < 1 - q := by linarith
  have hden : (0 : ℝ) < q ^ 2 + (1 - q) ^ 2 := by positivity
  simp only [bernVar, escortMap]
  rw [show (1 : ℝ) - 2 * (q * (1 - q)) = q ^ 2 + (1 - q) ^ 2 by ring]
  field_simp
  ring

/-- The probability with a prescribed Bernoulli variance. -/
noncomputable def probOfVar (w : ℝ) : ℝ := (1 - Real.sqrt (1 - 4 * w)) / 2

theorem probOfVar_mem {w : ℝ} (hw0 : 0 < w) (hw : w ≤ 1 / 4) :
    0 < probOfVar w ∧ probOfVar w < 1 := by
  have h1 : (0 : ℝ) ≤ 1 - 4 * w := by linarith
  have hlt : Real.sqrt (1 - 4 * w) < 1 := by
    have h := Real.sqrt_lt_sqrt h1 (show 1 - 4 * w < 1 by linarith)
    simpa using h
  have hnn : (0 : ℝ) ≤ Real.sqrt (1 - 4 * w) := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · rw [probOfVar]
    linarith
  · rw [probOfVar]
    linarith

theorem bernVar_probOfVar {w : ℝ} (hw : w ≤ 1 / 4) : bernVar (probOfVar w) = w := by
  have h1 : (0 : ℝ) ≤ 1 - 4 * w := by linarith
  have hsq : Real.sqrt (1 - 4 * w) ^ 2 = 1 - 4 * w := Real.sq_sqrt h1
  rw [bernVar, probOfVar]
  nlinarith [hsq]

/-- The two-site capacity in variance coordinates. -/
noncomputable def twoCapacity (a b K w₁ w₂ : ℝ) : ℝ := K * (w₁ * w₂) / (a * w₁ + b * w₂)

/-- **The two-site Schur capacity in variance coordinates.** -/
theorem schurCapacity_two (lam w : Fin 2 → ℝ) (hC : 0 < capC w lam) :
    schurCapacity w lam
      = twoCapacity (lam 0 ^ 2) (lam 1 ^ 2)
          (Real.pi ^ 2 * (lam 1 - lam 0) ^ 2) (w 0) (w 1) := by
  have hA : capA w = w 0 + w 1 := by simp [capA, Fin.sum_univ_two]
  have hB : capB w lam = w 0 * lam 0 + w 1 * lam 1 := by simp [capB, Fin.sum_univ_two]
  have hCv : capC w lam = w 0 * lam 0 ^ 2 + w 1 * lam 1 ^ 2 := by
    simp [capC, Fin.sum_univ_two]
  have hne : w 0 * lam 0 ^ 2 + w 1 * lam 1 ^ 2 ≠ 0 := by
    rw [← hCv]
    exact hC.ne'
  rw [schurCapacity_eq_ratio hC, twoCapacity, hA, hB, hCv]
  field_simp
  ring

/-- **Scalar capacity does not inherit escort transport.**  For every two-clock aperture there are
two variance states with the same capacity whose second escorts have different capacities, so no
scalar law `D ↦ ψ(D)` can describe the transport. -/
theorem no_scalar_descent {a b K : ℝ} (ha : 0 < a) (hb : 0 < b) (hK : 0 < K) :
    ∃ k c : ℝ, k * (2 * a + b) = 2 * a ∧ 0 < c ∧ c ≤ 1 / 8 ∧
      twoCapacity a b K c c = twoCapacity a b K (2 * c) (k * c)
        ∧ twoCapacity a b K (c ^ 2 / (1 - 2 * c) ^ 2) (c ^ 2 / (1 - 2 * c) ^ 2)
          ≠ twoCapacity a b K ((2 * c) ^ 2 / (1 - 2 * (2 * c)) ^ 2)
              ((k * c) ^ 2 / (1 - 2 * (k * c)) ^ 2) := by
  have hab : (0 : ℝ) < 2 * a + b := by linarith
  set k : ℝ := 2 * a / (2 * a + b) with hkdef
  have hkeq : k * (2 * a + b) = 2 * a := by
    rw [hkdef]
    field_simp
  have hk0 : 0 < k := by
    rw [hkdef]
    positivity
  have hk1 : k < 1 := by
    rw [hkdef, div_lt_one hab]
    linarith
  have hk2 : k ^ 2 * (2 * a + b) ^ 2 = 4 * a ^ 2 := by nlinarith [hkeq]
  have hkey : 4 * k ^ 2 * (a + b) < 4 * a + b * k ^ 2 := by
    nlinarith [hk2, mul_pos ha hb, mul_pos hb hb, hab, ha, hb]
  clear_value k
  clear hkdef
  set G₁ : ℝ → ℝ := fun c => K / ((a + b) * (1 - 2 * c) ^ 2) with hG1
  set G₂ : ℝ → ℝ := fun c =>
    4 * K * k ^ 2 / (4 * a * (1 - 2 * (k * c)) ^ 2 + b * k ^ 2 * (1 - 4 * c) ^ 2) with hG2
  have hd1 : (a + b) * (1 - 2 * (0 : ℝ)) ^ 2 ≠ 0 := by
    have h : (0 : ℝ) < a + b := by linarith
    simpa using h.ne'
  have hd2 : 4 * a * (1 - 2 * (k * (0 : ℝ))) ^ 2 + b * k ^ 2 * (1 - 4 * (0 : ℝ)) ^ 2 ≠ 0 := by
    have hpos : (0 : ℝ) < 4 * a + b * k ^ 2 := by positivity
    simpa using hpos.ne'
  have hcont1 : ContinuousAt G₁ 0 := by
    rw [hG1]
    exact ContinuousAt.div (by fun_prop) (by fun_prop) hd1
  have hcont2 : ContinuousAt G₂ 0 := by
    rw [hG2]
    exact ContinuousAt.div (by fun_prop) (by fun_prop) hd2
  have hval : G₁ 0 ≠ G₂ 0 := by
    rw [hG1, hG2]
    simp only [mul_zero, sub_zero, one_pow, mul_one]
    have hA : (0 : ℝ) < a + b := by linarith
    have hB : (0 : ℝ) < 4 * a + b * k ^ 2 := by positivity
    intro hcontra
    rw [div_eq_div_iff hA.ne' hB.ne'] at hcontra
    nlinarith [hcontra, hkey, hK]
  have hne0 : ∀ᶠ c in nhdsWithin (0 : ℝ) (Set.Ioi 0), G₁ c ≠ G₂ c := by
    have hsub : ContinuousAt (fun c => G₁ c - G₂ c) 0 := hcont1.sub hcont2
    have hne : (fun c => G₁ c - G₂ c) 0 ≠ 0 := sub_ne_zero.mpr hval
    have h := hsub.eventually_ne hne
    filter_upwards [h.filter_mono nhdsWithin_le_nhds] with c hc
    exact sub_ne_zero.mp hc
  have hsmall : ∀ᶠ c in nhdsWithin (0 : ℝ) (Set.Ioi 0), c < 1 / 8 := by
    have h : ∀ᶠ c in nhds (0 : ℝ), c < 1 / 8 :=
      eventually_lt_nhds (show (0 : ℝ) < 1 / 8 by norm_num)
    exact h.filter_mono nhdsWithin_le_nhds
  obtain ⟨c, ⟨hcne, hc8⟩, hc0⟩ := ((hne0.and hsmall).and self_mem_nhdsWithin).exists
  have hden1 : (1 : ℝ) - 2 * c ≠ 0 := by
    intro h
    have : c = 1 / 2 := by linarith
    linarith
  have hden2 : (1 : ℝ) - 4 * c ≠ 0 := by
    intro h
    have : c = 1 / 4 := by linarith
    linarith
  have hkc : k * c < 1 / 2 := by nlinarith
  have hden3 : (1 : ℝ) - 2 * (k * c) ≠ 0 := by
    intro h
    nlinarith [hkc]
  have hc2 : (c : ℝ) ^ 2 ≠ 0 := by positivity
  have hu : ((1 : ℝ) - 4 * c) ^ 2 ≠ 0 := pow_ne_zero 2 hden2
  have hv : ((1 : ℝ) - 2 * (k * c)) ^ 2 ≠ 0 := pow_ne_zero 2 hden3
  have hw : ((1 : ℝ) - 2 * c) ^ 2 ≠ 0 := pow_ne_zero 2 hden1
  have hA : (0 : ℝ) < a + b := by linarith
  have hD : (0 : ℝ) < 4 * a * (1 - 2 * (k * c)) ^ 2 + b * k ^ 2 * (1 - 4 * c) ^ 2 := by
    have h1 : (0 : ℝ) < (1 - 2 * (k * c)) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm hv)
    have h2 : (0 : ℝ) < (1 - 4 * c) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hu)
    positivity
  have hAne : (a + b) ≠ 0 := hA.ne'
  have hDne : 4 * a * (1 - 2 * (k * c)) ^ 2 + b * k ^ 2 * (1 - 4 * c) ^ 2 ≠ 0 := hD.ne'
  refine ⟨k, c, hkeq, hc0, hc8.le, ?_, ?_⟩
  · have hd1' : (0 : ℝ) < a * c + b * c := by nlinarith
    have hd2' : (0 : ℝ) < a * (2 * c) + b * (k * c) := by nlinarith
    rw [twoCapacity, twoCapacity, div_eq_div_iff hd1'.ne' hd2'.ne']
    linear_combination (-(K * c ^ 3)) * hkeq
  · have he1 : twoCapacity a b K (c ^ 2 / (1 - 2 * c) ^ 2) (c ^ 2 / (1 - 2 * c) ^ 2)
        = c ^ 2 * G₁ c := by
      rw [twoCapacity, hG1]
      simp only
      field_simp
    have he2 : twoCapacity a b K ((2 * c) ^ 2 / (1 - 2 * (2 * c)) ^ 2)
          ((k * c) ^ 2 / (1 - 2 * (k * c)) ^ 2) = c ^ 2 * G₂ c := by
      rw [twoCapacity, hG2]
      simp only
      rw [show (1 : ℝ) - 2 * (2 * c) = 1 - 4 * c by ring]
      set u : ℝ := (1 - 4 * c) ^ 2 with hudef
      set v : ℝ := (1 - 2 * (k * c)) ^ 2 with hvdef
      clear_value u v
      field_simp
      ring
    rw [he1, he2]
    intro hcontra
    exact hcne (mul_left_cancel₀ hc2 hcontra)

/-! ## Scalar capacity is blind to reflection -/

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- The Bernoulli variance vector is reflection invariant. -/
theorem bernoulliVarVec_one_sub (q : ι → ℝ) :
    (fun p => (1 - q p) * (1 - (1 - q p))) = fun p => q p * (1 - q p) := by
  funext p
  ring

/-- **Scalar capacity does not reconstruct the Gibbs state.** -/
theorem schurCapacity_one_sub (q lam : ι → ℝ) :
    schurCapacity (fun p => (1 - q p) * (1 - (1 - q p))) lam
      = schurCapacity (fun p => q p * (1 - q p)) lam := by
  rw [bernoulliVarVec_one_sub]

end HTGeometry.ConstraintFrameRelativity
