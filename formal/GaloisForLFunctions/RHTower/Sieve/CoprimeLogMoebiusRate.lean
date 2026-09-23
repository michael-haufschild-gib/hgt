import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusOneRate
import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusLimit

/-!
# Quantitative coprime logarithmic Möbius rates

A bounded solution of the divided-argument prime recursion inherits an inverse-log-square error
rate.  Strong induction on the integer cutoff supplies the growing unroll: beyond `p⁴`, scaling by
`p` contracts the weighted error by at most `8/9`.  Prime peeling then propagates the modulus-one
rate to every fixed squarefree modulus.
-/

namespace RHTower.Sieve

open Filter Topology

/-- A bounded divided-argument contraction preserves an eventual inverse-log-square rate. -/
theorem exists_abs_sub_eulerFactor_mul_log_sq_rate_of_div_contraction
    (p : ℕ) (hp : p.Prime) (f g : ℝ → ℝ) (L C G : ℝ)
    (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hf : ∀ Y : ℝ, |f Y| ≤ C)
    (hg : ∀ᶠ Y : ℝ in atTop, |g Y - L| ≤ G / (Real.log Y) ^ (2 : ℕ))
    (hrec : ∀ Y : ℝ,
      g Y = f Y - (1 / (p : ℝ)) * f (Y / (p : ℝ))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ Y : ℝ in atTop,
      |f Y - ((p : ℝ) / ((p : ℝ) - 1)) * L| ≤ D / (Real.log Y) ^ (2 : ℕ) := by
  rw [Filter.eventually_atTop] at hg
  obtain ⟨Y₀, hY₀⟩ := hg
  let pR : ℝ := p
  let A : ℝ := (pR / (pR - 1)) * L
  let T : ℝ := max Y₀ (max (pR ^ (4 : ℕ)) (Real.exp 1))
  let D : ℝ := 9 * G + (C + |A|) * (Real.log (pR * T)) ^ (2 : ℕ)
  have hpR2 : (2 : ℝ) ≤ pR := by
    dsimp [pR]
    exact_mod_cast hp.two_le
  have hpR1 : (1 : ℝ) < pR := lt_of_lt_of_le one_lt_two hpR2
  have hpR0 : 0 < pR := lt_trans zero_lt_one hpR1
  have hT_Y₀ : Y₀ ≤ T := le_trans (le_max_left Y₀ (max (pR ^ (4 : ℕ)) (Real.exp 1))) le_rfl
  have hT_p4 : pR ^ (4 : ℕ) ≤ T :=
    le_trans (le_max_left (pR ^ (4 : ℕ)) (Real.exp 1))
      (le_max_right Y₀ (max (pR ^ (4 : ℕ)) (Real.exp 1)))
  have hT_exp : Real.exp 1 ≤ T :=
    le_trans (le_max_right (pR ^ (4 : ℕ)) (Real.exp 1))
      (le_max_right Y₀ (max (pR ^ (4 : ℕ)) (Real.exp 1)))
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos 1) hT_exp
  have hlog_pT0 : 0 < Real.log (pR * T) := by
    apply Real.log_pos
    have : 1 < pR * T := by nlinarith [Real.exp_pos 1, Real.one_lt_exp_iff.mpr zero_lt_one]
    exact this
  have hAden : pR - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hpR1)
  have hfixed : L = A - (1 / pR) * A := by
    dsimp [A]
    field_simp
  have herr (Y : ℝ) :
      f Y - A = (g Y - L) + (1 / pR) * (f (Y / pR) - A) := by
    rw [hrec, hfixed]
    dsimp [pR]
    ring
  have hD : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg (mul_nonneg (by norm_num) hG)
      (mul_nonneg (add_nonneg hC (abs_nonneg A)) (sq_nonneg _))
  refine ⟨D, hD, ?_⟩
  filter_upwards [eventually_ge_atTop T] with Y hTY
  have hmain : ∀ n : ℕ, ∀ Z : ℝ, ⌊Z⌋₊ = n → T ≤ Z →
      |f Z - A| ≤ D / (Real.log Z) ^ (2 : ℕ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro Z hfloor hTZ
      have hZexp : Real.exp 1 ≤ Z := le_trans hT_exp hTZ
      have hZ1 : 1 < Z := lt_of_lt_of_le
        (Real.one_lt_exp_iff.mpr zero_lt_one) hZexp
      have hZ0 : 0 < Z := lt_trans zero_lt_one hZ1
      have hlogZ : 1 ≤ Real.log Z := by
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) hZexp
      have hlogZ0 : 0 < Real.log Z := lt_of_lt_of_le zero_lt_one hlogZ
      have hgZ : |g Z - L| ≤ G / (Real.log Z) ^ (2 : ℕ) :=
        hY₀ Z (le_trans hT_Y₀ hTZ)
      rw [herr]
      calc
        |(g Z - L) + (1 / pR) * (f (Z / pR) - A)| ≤
            |g Z - L| + |(1 / pR) * (f (Z / pR) - A)| := abs_add_le _ _
        _ ≤ G / (Real.log Z) ^ (2 : ℕ) + |(1 / pR) * (f (Z / pR) - A)| :=
          add_le_add hgZ le_rfl
        _ ≤ D / (Real.log Z) ^ (2 : ℕ) := by
          rcases le_or_gt T (Z / pR) with hchild | hbase
          · have hfloorChild : ⌊Z / pR⌋₊ = n / p := by
              dsimp [pR]
              rw [Nat.floor_div_natCast, hfloor]
            have hn0 : 0 < n := by
              rw [← hfloor, Nat.floor_pos]
              exact hZ1.le
            have hchildlt : n / p < n := Nat.div_lt_self hn0 hp.one_lt
            have hIH : |f (Z / pR) - A| ≤
                D / (Real.log (Z / pR)) ^ (2 : ℕ) := by
              exact ih (n / p) hchildlt (Z / pR) hfloorChild hchild
            have hchild0 : 0 < Z / pR := div_pos hZ0 hpR0
            have hp4Z : pR ^ (4 : ℕ) ≤ Z := le_trans hT_p4 hTZ
            have hlogp0 : 0 < Real.log pR := Real.log_pos hpR1
            have hlogp4 : 4 * Real.log pR ≤ Real.log Z := by
              have hmono := Real.log_le_log (pow_pos hpR0 4) hp4Z
              rw [Real.log_pow] at hmono
              norm_num at hmono
              exact hmono
            have hlogdiv : Real.log (Z / pR) = Real.log Z - Real.log pR :=
              Real.log_div hZ0.ne' hpR0.ne'
            have hlogchild : (3 / 4 : ℝ) * Real.log Z ≤ Real.log (Z / pR) := by
              rw [hlogdiv]
              linarith
            have hlogchild0 : 0 < Real.log (Z / pR) :=
              lt_of_lt_of_le (mul_pos (by norm_num) hlogZ0) hlogchild
            have hsq : (9 / 16 : ℝ) * (Real.log Z) ^ (2 : ℕ) ≤
                (Real.log (Z / pR)) ^ (2 : ℕ) := by
              nlinarith [sq_nonneg (Real.log (Z / pR) - (3 / 4 : ℝ) * Real.log Z)]
            have hrecip : 1 / (Real.log (Z / pR)) ^ (2 : ℕ) ≤
                (16 / 9 : ℝ) / (Real.log Z) ^ (2 : ℕ) := by
              rw [div_le_div_iff₀ (pow_pos hlogchild0 2) (pow_pos hlogZ0 2)]
              nlinarith
            have hq : 1 / pR ≤ (1 / 2 : ℝ) := by
              exact one_div_le_one_div_of_le (by norm_num) hpR2
            have hchildTerm : |(1 / pR) * (f (Z / pR) - A)| ≤
                (8 / 9 : ℝ) * D / (Real.log Z) ^ (2 : ℕ) := by
              rw [abs_mul, abs_of_pos (one_div_pos.mpr hpR0)]
              calc
                (1 / pR) * |f (Z / pR) - A| ≤
                    (1 / pR) * (D / (Real.log (Z / pR)) ^ (2 : ℕ)) :=
                  mul_le_mul_of_nonneg_left hIH (one_div_nonneg.mpr hpR0.le)
                _ ≤ (1 / pR) * (D * ((16 / 9 : ℝ) / (Real.log Z) ^ (2 : ℕ))) := by
                  rw [div_eq_mul_inv]
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left
                      (by simpa only [one_div] using hrecip) hD)
                    (one_div_nonneg.mpr hpR0.le)
                _ ≤ (1 / 2 : ℝ) * (D * ((16 / 9 : ℝ) / (Real.log Z) ^ (2 : ℕ))) := by
                  exact mul_le_mul_of_nonneg_right hq
                    (mul_nonneg hD (div_nonneg (by norm_num) (pow_nonneg hlogZ0.le 2)))
                _ = (8 / 9 : ℝ) * D / (Real.log Z) ^ (2 : ℕ) := by ring
            calc
              G / (Real.log Z) ^ (2 : ℕ) + |(1 / pR) * (f (Z / pR) - A)| ≤
                  G / (Real.log Z) ^ (2 : ℕ) +
                    (8 / 9 : ℝ) * D / (Real.log Z) ^ (2 : ℕ) :=
                add_le_add le_rfl hchildTerm
              _ ≤ D / (Real.log Z) ^ (2 : ℕ) := by
                have hGD : 9 * G ≤ D := by
                  dsimp [D]
                  have hrest : 0 ≤ (C + |A|) * (Real.log (pR * T)) ^ (2 : ℕ) :=
                    mul_nonneg (add_nonneg hC (abs_nonneg A)) (sq_nonneg _)
                  linarith
                have hden : 0 < (Real.log Z) ^ (2 : ℕ) := pow_pos hlogZ0 2
                calc
                  G / (Real.log Z) ^ (2 : ℕ) + (8 / 9 : ℝ) * D / (Real.log Z) ^ (2 : ℕ) =
                      (G + (8 / 9 : ℝ) * D) / (Real.log Z) ^ (2 : ℕ) := by ring
                  _ ≤ D / (Real.log Z) ^ (2 : ℕ) :=
                    div_le_div_of_nonneg_right (by nlinarith) hden.le
          · have hZpT : Z < pR * T := by
              rw [div_lt_iff₀ hpR0] at hbase
              simpa [mul_comm] using hbase
            have hlogZpT : Real.log Z ≤ Real.log (pR * T) :=
              Real.log_le_log hZ0 hZpT.le
            have hsqlog : (Real.log Z) ^ (2 : ℕ) ≤ (Real.log (pR * T)) ^ (2 : ℕ) :=
              pow_le_pow_left₀ hlogZ0.le hlogZpT 2
            have hfA : |f (Z / pR) - A| ≤ C + |A| := by
              exact le_trans (abs_sub _ _) (add_le_add (hf _) le_rfl)
            have hbaseTerm : |(1 / pR) * (f (Z / pR) - A)| ≤
                ((C + |A|) * (Real.log (pR * T)) ^ (2 : ℕ)) /
                  (Real.log Z) ^ (2 : ℕ) := by
              rw [abs_mul, abs_of_pos (one_div_pos.mpr hpR0)]
              have hq1 : 1 / pR ≤ 1 := (div_le_one hpR0).mpr hpR1.le
              have hraw : (1 / pR) * |f (Z / pR) - A| ≤ C + |A| := by
                calc
                  (1 / pR) * |f (Z / pR) - A| ≤ 1 * |f (Z / pR) - A| :=
                    mul_le_mul_of_nonneg_right hq1 (abs_nonneg _)
                  _ ≤ C + |A| := by simpa using hfA
              rw [le_div_iff₀ (pow_pos hlogZ0 2)]
              calc
                (1 / pR) * |f (Z / pR) - A| * (Real.log Z) ^ (2 : ℕ) ≤
                    (C + |A|) * (Real.log Z) ^ (2 : ℕ) :=
                  mul_le_mul_of_nonneg_right hraw (pow_nonneg hlogZ0.le 2)
                _ ≤ (C + |A|) * (Real.log (pR * T)) ^ (2 : ℕ) :=
                  mul_le_mul_of_nonneg_left hsqlog (add_nonneg hC (abs_nonneg A))
            calc
              G / (Real.log Z) ^ (2 : ℕ) + |(1 / pR) * (f (Z / pR) - A)| ≤
                  G / (Real.log Z) ^ (2 : ℕ) +
                    ((C + |A|) * (Real.log (pR * T)) ^ (2 : ℕ)) /
                      (Real.log Z) ^ (2 : ℕ) := add_le_add le_rfl hbaseTerm
              _ ≤ D / (Real.log Z) ^ (2 : ℕ) := by
                have hnum : G + (C + |A|) * (Real.log (pR * T)) ^ (2 : ℕ) ≤ D := by
                  dsimp [D]
                  nlinarith
                calc
                  G / (Real.log Z) ^ (2 : ℕ) +
                      ((C + |A|) * (Real.log (pR * T)) ^ (2 : ℕ)) / (Real.log Z) ^ (2 : ℕ) =
                    (G + (C + |A|) * (Real.log (pR * T)) ^ (2 : ℕ)) /
                      (Real.log Z) ^ (2 : ℕ) := by ring
                  _ ≤ D / (Real.log Z) ^ (2 : ℕ) :=
                    div_le_div_of_nonneg_right hnum (pow_nonneg hlogZ0.le 2)
  exact hmain ⌊Y⌋₊ Y rfl hTY

/-- A quantitative rate at one squarefree modulus propagates across one new prime factor. -/
theorem exists_abs_coprimeLogMoebius_prime_step_sub_totient_log_sq_rate
    {p e : ℕ} (hp : p.Prime) (hpe : ¬ p ∣ e) (he : Squarefree (p * e))
    {G : ℝ} (hG : 0 ≤ G)
    (hrate : ∀ᶠ Y : ℝ in atTop,
      |coprimeLogMoebius e Y -
        ((e : ℝ) / (Nat.totient e : ℝ))| ≤ G / (Real.log Y) ^ (2 : ℕ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ Y : ℝ in atTop,
      |coprimeLogMoebius (p * e) Y -
        (((p * e : ℕ) : ℝ) / (Nat.totient (p * e) : ℝ))| ≤
          D / (Real.log Y) ^ (2 : ℕ) := by
  let C : ℝ := coprimeLogMoebiusConst *
    (((p * e : ℕ) : ℝ) / (Nat.totient (p * e) : ℝ))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg coprimeLogMoebiusConst_nonneg
      (div_nonneg (by positivity) (by positivity))
  obtain ⟨D, hD, hrateD⟩ :=
    exists_abs_sub_eulerFactor_mul_log_sq_rate_of_div_contraction
      p hp (coprimeLogMoebius (p * e)) (coprimeLogMoebius e)
      ((e : ℝ) / (Nat.totient e : ℝ)) C G hC hG
      (abs_coprimeLogMoebius_le (p * e) he) hrate
      (coprimeLogMoebius_recursion hp hpe)
  have hcop : Nat.Coprime p e := (hp.coprime_iff_not_dvd).mpr hpe
  have he0 : e ≠ 0 := by
    intro hezero
    rw [hezero, Nat.mul_zero] at he
    exact he.ne_zero rfl
  have htot : Nat.totient (p * e) = (p - 1) * Nat.totient e := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hp]
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hcastSub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp1, Nat.cast_one]
  have htotpos : (0 : ℝ) < (Nat.totient e : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero he0)
  have hppos : (0 : ℝ) < (p : ℝ) - 1 := by
    have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    linarith
  have htarget :
      ((p : ℝ) / ((p : ℝ) - 1)) *
          ((e : ℝ) / (Nat.totient e : ℝ)) =
        (((p * e : ℕ) : ℝ) / (Nat.totient (p * e) : ℝ)) := by
    rw [htot]
    push_cast
    rw [hcastSub]
    field_simp
  refine ⟨D, hD, ?_⟩
  filter_upwards [hrateD] with Y hY
  rwa [htarget] at hY

/-- Every fixed squarefree modulus has the quantitative two-logarithm coprime Möbius rate. -/
theorem exists_abs_coprimeLogMoebius_squarefree_sub_totient_log_sq_rate :
    ∀ e : ℕ, Squarefree e →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Y : ℝ in atTop,
        |coprimeLogMoebius e Y -
          ((e : ℝ) / (Nat.totient e : ℝ))| ≤ C / (Real.log Y) ^ (2 : ℕ) := by
  intro e
  induction e using Nat.strong_induction_on with
  | h e ih =>
    intro he
    rcases eq_or_ne e 1 with rfl | hne
    · simpa using exists_abs_coprimeLogMoebius_one_sub_one_log_sq_rate
    · have he0 : e ≠ 0 := he.ne_zero
      let p := e.minFac
      let e' := e / p
      have hp : p.Prime := Nat.minFac_prime hne
      have hpd : p ∣ e := Nat.minFac_dvd e
      have hmul : p * e' = e := Nat.mul_div_cancel' hpd
      have hpe : ¬ p ∣ e' := by
        intro hdvd
        obtain ⟨k, hk⟩ := hdvd
        have hsq : p * p ∣ e := by
          refine ⟨k, ?_⟩
          calc
            e = p * e' := hmul.symm
            _ = p * (p * k) := by rw [hk]
            _ = p * p * k := by ring
        have hunit := he _ hsq
        rw [Nat.isUnit_iff] at hunit
        exact hp.ne_one hunit
      have he'Sf : Squarefree e' :=
        Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hpd) he
      have he'lt : e' < e := Nat.div_lt_self (Nat.pos_of_ne_zero he0) hp.one_lt
      obtain ⟨G, hG, hrate⟩ := ih e' he'lt he'Sf
      have hprod : Squarefree (p * e') := by rwa [hmul]
      obtain ⟨D, hD, hstep⟩ :=
        exists_abs_coprimeLogMoebius_prime_step_sub_totient_log_sq_rate
          hp hpe hprod hG hrate
      refine ⟨D, hD, ?_⟩
      simpa only [hmul] using hstep

end RHTower.Sieve
