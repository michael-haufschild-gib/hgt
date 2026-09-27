import GaloisForLFunctions.RHTower.MobiusCubicGammaNorm
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Frequency jets of the cubic source atom and Taylor packets

The frequency derivatives of `f_x(t) = x² e^{-x t}` are

`∂_x^r f_x(t) = e^{-x t} (x² (-t)^r + 2 r x (-t)^(r-1) + r (r-1) (-t)^(r-2))`.

Uniformly for `0 ≤ δ ≤ 1` their cubic Gamma norms obey
`‖∂_x^r f_x‖_δ ≤ C_r x^(-r-1/2-δ/2)`, and the order-`d` Taylor remainder of `b ↦ f_b` at `a`
has norm at most `C_d (b-a)^d (b/a)² a^(-d-1/2-δ/2) / d!`.  The block Taylor law bounds a
finite signed atom packet supported in `[X, X+L]` by its centred moments and a remainder.
-/

open MeasureTheory Set Filter Finset

noncomputable section

namespace RHTower.CubicGamma

/-! ### Taylor remainder for an explicit derivative chain -/

private theorem hasDerivAt_taylor_term (c a : ℝ) (d : ℕ) (y : ℝ) :
    HasDerivAt (fun y => c * (y - a) ^ (d + 1) / ((d + 1).factorial : ℝ))
      (c * (y - a) ^ d / (d.factorial : ℝ)) y := by
  have h := (((hasDerivAt_id y).sub_const a).pow (d + 1)).const_mul c |>.div_const
    ((d + 1).factorial : ℝ)
  refine h.congr_deriv ?_
  simp only [id_eq, Nat.add_sub_cancel, mul_one, Nat.factorial_succ, Nat.cast_mul]
  have hf : (d.factorial : ℝ) ≠ 0 := by positivity
  field_simp

private theorem hasDerivAt_taylorPoly (g : ℕ → ℝ → ℝ) (a : ℝ) (d : ℕ) (y : ℝ) :
    HasDerivAt (fun y => ∑ j ∈ range (d + 1), g j a * (y - a) ^ j / (j.factorial : ℝ))
      (∑ j ∈ range d, g (j + 1) a * (y - a) ^ j / (j.factorial : ℝ)) y := by
  induction d with
  | zero =>
      simp only [zero_add, range_one, sum_singleton, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, mul_one, range_zero, sum_empty]
      exact hasDerivAt_const _ _
  | succ d ih =>
      have ht := hasDerivAt_taylor_term (g (d + 1) a) a d y
      have hs := ih.add ht
      have e : (fun y => ∑ j ∈ range (d + 1 + 1), g j a * (y - a) ^ j / (j.factorial : ℝ)) =
          (fun y => ∑ j ∈ range (d + 1), g j a * (y - a) ^ j / (j.factorial : ℝ)) +
            fun y => g (d + 1) a * (y - a) ^ (d + 1) / ((d + 1).factorial : ℝ) := by
        funext z
        rw [sum_range_succ, Pi.add_apply]
      rw [e, sum_range_succ]
      exact hs

/-- **Taylor bound for a derivative chain.**  If `g (k+1)` is the derivative of `g k` everywhere
and `|g d| ≤ M` on `[a,b]`, the order-`d` Taylor remainder at `a` is at most
`M (b-a)^d / d!`. -/
theorem abs_taylor_chain_le {g : ℕ → ℝ → ℝ} (hg : ∀ k x, HasDerivAt (g k) (g (k + 1) x) x)
    (d : ℕ) {a b M : ℝ} (hab : a ≤ b) (hM : ∀ y ∈ Icc a b, |g d y| ≤ M) :
    |g 0 b - ∑ j ∈ range d, g j a * (b - a) ^ j / (j.factorial : ℝ)| ≤
      M * (b - a) ^ d / (d.factorial : ℝ) := by
  induction d generalizing g b with
  | zero =>
      simpa using hM b ⟨hab, le_rfl⟩
  | succ d ih =>
      set h : ℝ → ℝ := fun y => g 0 y - ∑ j ∈ range (d + 1), g j a * (y - a) ^ j /
        (j.factorial : ℝ) with hh
      set h' : ℝ → ℝ := fun y => g 1 y - ∑ j ∈ range d, g (j + 1) a * (y - a) ^ j /
        (j.factorial : ℝ) with hh'
      have hder : ∀ y, HasDerivAt h (h' y) y := fun y =>
        (hg 0 y).sub (hasDerivAt_taylorPoly g a d y)
      have hbound : ∀ y ∈ Ico a b, ‖h' y‖ ≤ M * (y - a) ^ d / (d.factorial : ℝ) := by
        intro y hy
        have hg' : ∀ k x, HasDerivAt (fun z => g (k + 1) z) (g (k + 1 + 1) x) x :=
          fun k x => hg (k + 1) x
        have := ih (g := fun k => g (k + 1)) hg' (b := y) hy.1 (fun z hz => hM z
          ⟨hz.1, hz.2.trans hy.2.le⟩)
        simpa [Real.norm_eq_abs, hh'] using this
      have hB : ∀ x, HasDerivAt (fun y => M * (y - a) ^ (d + 1) / ((d + 1).factorial : ℝ))
          (M * (x - a) ^ d / (d.factorial : ℝ)) x := fun x => hasDerivAt_taylor_term M a d x
      have ha : ‖h a‖ ≤ M * (a - a) ^ (d + 1) / ((d + 1).factorial : ℝ) := by
        simp only [hh, sub_self, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          not_false_eq_true, zero_pow, mul_zero, zero_div, norm_le_zero_iff]
        rw [sum_range_succ']
        simp
      have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
        (f := h) (a := a) (b := b) (f' := h')
        (fun y _ => (hder y).continuousAt.continuousWithinAt)
        (fun y _ => (hder y).hasDerivWithinAt) ha hB hbound ⟨hab, le_rfl⟩
      simpa [Real.norm_eq_abs, hh] using key

/-! ### Frequency jets of the atom -/

/-- The `r`-th frequency derivative of the source atom. -/
def atomJet (r : ℕ) (x t : ℝ) : ℝ :=
  Real.exp (-(x * t)) *
    (x ^ 2 * (-t) ^ r + 2 * r * x * (-t) ^ (r - 1) + r * (r - 1 : ℝ) * (-t) ^ (r - 2))

theorem atomJet_zero (x t : ℝ) : atomJet 0 x t = atom x t := by
  simp [atomJet, atom, mul_comm]

theorem continuous_atomJet (r : ℕ) (x : ℝ) : Continuous (atomJet r x) := by
  unfold atomJet
  fun_prop

theorem hasDerivAt_atomJet (r : ℕ) (t x : ℝ) :
    HasDerivAt (fun x => atomJet r x t) (atomJet (r + 1) x t) x := by
  have he : HasDerivAt (fun x => Real.exp (-(x * t))) (Real.exp (-(x * t)) * (-t)) x := by
    have := ((hasDerivAt_id x).mul_const t).neg.exp
    simpa using this
  have hp : HasDerivAt
      (fun x => x ^ 2 * (-t) ^ r + 2 * r * x * (-t) ^ (r - 1) + r * (r - 1 : ℝ) * (-t) ^ (r - 2))
      (2 * x * (-t) ^ r + 2 * r * (-t) ^ (r - 1)) x := by
    have h1 := ((hasDerivAt_pow 2 x).mul_const ((-t) ^ r))
    have h2 := (((hasDerivAt_id x).const_mul (2 * (r : ℝ))).mul_const ((-t) ^ (r - 1)))
    have h3 := hasDerivAt_const x ((r : ℝ) * (r - 1 : ℝ) * (-t) ^ (r - 2))
    refine ((h1.add h2).add h3).congr_deriv ?_
    simp only [Nat.cast_ofNat]
    ring
  refine (he.mul hp).congr_deriv ?_
  unfold atomJet
  rcases r with _ | _ | r
  · simp; ring
  · simp; ring
  · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, show r + 1 + 1 + 1 - 2 = r + 1 by
      omega, show r + 1 + 1 - 2 = r by omega, show r + 1 + 1 - 1 = r + 1 by omega, pow_succ]
    ring

/-- The pointwise envelope of `∂^r f_ξ(t)` for `a ≤ ξ ≤ b`. -/
def jetEnvelope (r : ℕ) (a b t : ℝ) : ℝ :=
  b ^ 2 * expMono r a t + 2 * r * b * expMono (r - 1) a t + r * (r - 1 : ℝ) * expMono (r - 2) a t

theorem abs_atomJet_le {r : ℕ} {a b ξ t : ℝ} (ha : 0 < a) (haξ : a ≤ ξ) (hξb : ξ ≤ b)
    (ht : 0 < t) :
    |atomJet r ξ t| ≤ jetEnvelope r a b t := by
  have hξ : 0 < ξ := ha.trans_le haξ
  have hexp : Real.exp (-(ξ * t)) ≤ Real.exp (-(a * t)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hr1 : (0 : ℝ) ≤ (r : ℝ) * (r - 1 : ℝ) := by
    rcases r with _ | r
    · simp
    · push_cast; nlinarith
  unfold atomJet jetEnvelope expMono
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hpoly : |ξ ^ 2 * (-t) ^ r + 2 * r * ξ * (-t) ^ (r - 1) + r * (r - 1 : ℝ) * (-t) ^ (r - 2)|
      ≤ b ^ 2 * t ^ r + 2 * r * b * t ^ (r - 1) + r * (r - 1 : ℝ) * t ^ (r - 2) := by
    have e1 : |(-t) ^ r| = t ^ r := by rw [abs_pow, abs_neg, abs_of_pos ht]
    have e2 : |(-t) ^ (r - 1)| = t ^ (r - 1) := by rw [abs_pow, abs_neg, abs_of_pos ht]
    have e3 : |(-t) ^ (r - 2)| = t ^ (r - 2) := by rw [abs_pow, abs_neg, abs_of_pos ht]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [abs_mul, e1, abs_of_nonneg (sq_nonneg ξ)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hξ.le hξb 2) (by positivity)
    · rw [abs_mul, e2, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * r),
        abs_of_pos hξ]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hξb (by positivity))
        (by positivity)
    · rw [abs_mul, e3, abs_of_nonneg hr1]
  have hpos : 0 ≤ b ^ 2 * t ^ r + 2 * r * b * t ^ (r - 1) + r * (r - 1 : ℝ) * t ^ (r - 2) := by
    have hb : 0 ≤ b := (hξ.trans_le hξb).le
    positivity
  calc Real.exp (-(ξ * t)) * |ξ ^ 2 * (-t) ^ r + 2 * r * ξ * (-t) ^ (r - 1) +
        r * (r - 1 : ℝ) * (-t) ^ (r - 2)|
      ≤ Real.exp (-(a * t)) *
        (b ^ 2 * t ^ r + 2 * r * b * t ^ (r - 1) + r * (r - 1 : ℝ) * t ^ (r - 2)) :=
        mul_le_mul hexp hpoly (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

/-! ### Norms of the jets -/

/-- `Γ(5+δ) ≥ 24` and `Γ(5+δ+2j) ≤ Γ(6+2r)` for `0 ≤ δ ≤ 1`, `j ≤ r`. -/
theorem gamma_ratio_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {j r : ℕ} (hj : j ≤ r) :
    Real.Gamma (5 + δ + 2 * j) / Real.Gamma (5 + δ) ≤ Real.Gamma (6 + 2 * r) / 24 := by
  have hmono := Real.Gamma_strictMonoOn_Ici.monotoneOn
  have h24 : (24 : ℝ) ≤ Real.Gamma (5 + δ) := by
    have h5 : Real.Gamma 5 = 24 := by
      rw [show (5 : ℝ) = (4 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
      norm_num [Nat.factorial]
    rw [← h5]
    exact hmono (Set.mem_Ici.mpr (by norm_num)) (Set.mem_Ici.mpr (by linarith)) (by linarith)
  have hjr : (j : ℝ) ≤ r := by exact_mod_cast hj
  have hnum : Real.Gamma (5 + δ + 2 * j) ≤ Real.Gamma (6 + 2 * r) :=
    hmono (Set.mem_Ici.mpr (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]))
      (Set.mem_Ici.mpr (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])) (by linarith)
  have hg0 : 0 < Real.Gamma (5 + δ + 2 * j) := Real.Gamma_pos_of_pos (by positivity)
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith

/-- The Gamma constant attached to jets of order at most `r`. -/
def monoConst (r : ℕ) : ℝ := Real.sqrt (Real.Gamma (6 + 2 * r) / 24)

theorem monoConst_nonneg (r : ℕ) : 0 ≤ monoConst r := Real.sqrt_nonneg _

/-- `‖t^j e^{-a t}‖_δ ≤ K_r a^(-(5+δ)/2) / a^j` for `j ≤ r`, uniformly in `0 ≤ δ ≤ 1`. -/
theorem gammaNorm_expMono_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {j r : ℕ} (hj : j ≤ r)
    {a : ℝ} (ha : 0 < a) :
    gammaNorm δ (expMono j a) ≤ monoConst r * (a ^ ((5 + δ) / 2))⁻¹ / a ^ j := by
  have hδ : 0 < 5 + δ := by linarith
  have hE : gammaEnergy δ (expMono j a) ≤
      Real.Gamma (6 + 2 * r) / 24 * ((a ^ ((5 + δ) / 2))⁻¹ / a ^ j) ^ 2 := by
    rw [gammaEnergy_expMono hδ j ha]
    have hg := gamma_ratio_le hδ0 hδ1 hj
    have hg5 := Real.Gamma_pos_of_pos hδ
    have hgn : 0 < Real.Gamma (5 + δ + 2 * j) := Real.Gamma_pos_of_pos (by positivity)
    have hpow : a ^ (5 + δ + 2 * (j : ℝ)) ≤ (2 * a) ^ (5 + δ + 2 * (j : ℝ)) :=
      Real.rpow_le_rpow ha.le (by linarith) (by positivity)
    have hsplit : ((a ^ ((5 + δ) / 2))⁻¹ / a ^ j) ^ 2 = (a ^ (5 + δ + 2 * (j : ℝ)))⁻¹ := by
      rw [Real.rpow_add ha, show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, div_pow, inv_pow, ← Real.rpow_natCast (a ^ ((5 + δ) / 2)) 2,
        ← Real.rpow_mul ha.le]
      rw [show (5 + δ) / 2 * ((2 : ℕ) : ℝ) = 5 + δ by push_cast; ring, pow_mul]
      field_simp
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [hsplit]
    have hapos : 0 < a ^ (5 + δ + 2 * (j : ℝ)) := Real.rpow_pos_of_pos ha _
    calc Real.Gamma (5 + δ + 2 * j) / (Real.Gamma (5 + δ) * (2 * a) ^ (5 + δ + 2 * (j : ℝ)))
        ≤ Real.Gamma (5 + δ + 2 * j) / (Real.Gamma (5 + δ) * a ^ (5 + δ + 2 * (j : ℝ))) := by
          apply div_le_div_of_nonneg_left hgn.le (by positivity)
          exact mul_le_mul_of_nonneg_left hpow hg5.le
      _ = Real.Gamma (5 + δ + 2 * j) / Real.Gamma (5 + δ) * (a ^ (5 + δ + 2 * (j : ℝ)))⁻¹ := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hg (by positivity)
  unfold gammaNorm monoConst
  calc Real.sqrt (gammaEnergy δ (expMono j a))
      ≤ Real.sqrt (Real.Gamma (6 + 2 * r) / 24 * ((a ^ ((5 + δ) / 2))⁻¹ / a ^ j) ^ 2) :=
        Real.sqrt_le_sqrt hE
    _ = _ := by
      rw [Real.sqrt_mul (by
          have : 0 < Real.Gamma (6 + 2 * r) := Real.Gamma_pos_of_pos (by positivity)
          positivity), Real.sqrt_sq (by positivity)]
      ring

theorem one_div_pow_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {r k : ℕ} (hk : k ≤ r) :
    1 / a ^ (r - k) ≤ b ^ k / a ^ r := by
  have hsplit : a ^ r = a ^ k * a ^ (r - k) := by rw [← pow_add, Nat.add_sub_cancel' hk]
  rw [hsplit, show b ^ k / (a ^ k * a ^ (r - k)) = (b / a) ^ k * (1 / a ^ (r - k)) by
    rw [div_pow]; field_simp]
  have h1 : 1 ≤ (b / a) ^ k := one_le_pow₀ ((one_le_div ha).mpr hab)
  have h0 : 0 ≤ 1 / a ^ (r - k) := by positivity
  nlinarith

/-- The jet constant `C_r = (1+r)² K_r`. -/
def jetConst (r : ℕ) : ℝ := (1 + r) ^ 2 * monoConst r

theorem jetConst_nonneg (r : ℕ) : 0 ≤ jetConst r := by
  unfold jetConst
  have := monoConst_nonneg r
  positivity

theorem gammaFinite_jetEnvelope {δ : ℝ} (hδ : 0 < 5 + δ) (r : ℕ) {a : ℝ} (ha : 0 < a)
    (b : ℝ) : GammaFinite δ (jetEnvelope r a b) := by
  unfold jetEnvelope
  exact (((gammaFinite_expMono hδ r ha).smul _).add ((gammaFinite_expMono hδ (r - 1) ha).smul _)).add
    ((gammaFinite_expMono hδ (r - 2) ha).smul _)

/-- **Envelope norm law.**  For `0 < a ≤ b` and `0 ≤ δ ≤ 1`,
`‖envelope‖_δ ≤ C_r b² a^(-(5+δ)/2) / a^r`. -/
theorem gammaNorm_jetEnvelope_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (r : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    gammaNorm δ (jetEnvelope r a b) ≤ jetConst r * b ^ 2 * (a ^ ((5 + δ) / 2))⁻¹ / a ^ r := by
  have hδ : 0 < 5 + δ := by linarith
  have hb : 0 < b := ha.trans_le hab
  have f0 := gammaFinite_expMono hδ r ha
  have f1 := gammaFinite_expMono hδ (r - 1) ha
  have f2 := gammaFinite_expMono hδ (r - 2) ha
  have n0 := gammaNorm_expMono_le hδ0 hδ1 (le_refl r) ha
  have n1 := gammaNorm_expMono_le hδ0 hδ1 (Nat.sub_le r 1) ha
  have n2 := gammaNorm_expMono_le hδ0 hδ1 (Nat.sub_le r 2) ha
  set A := (a ^ ((5 + δ) / 2))⁻¹ with hA
  have hA0 : 0 ≤ A := by positivity
  have hK := monoConst_nonneg r
  have hr1 : (0 : ℝ) ≤ (r : ℝ) * (r - 1 : ℝ) := by
    rcases r with _ | r
    · simp
    · push_cast; nlinarith
  have htri : gammaNorm δ (jetEnvelope r a b) ≤
      b ^ 2 * gammaNorm δ (expMono r a) + 2 * r * b * gammaNorm δ (expMono (r - 1) a) +
        r * (r - 1 : ℝ) * gammaNorm δ (expMono (r - 2) a) := by
    unfold jetEnvelope
    refine (gammaNorm_add_le hδ ((f0.smul _).add (f1.smul _)) (f2.smul _)).trans ?_
    refine add_le_add ((gammaNorm_add_le hδ (f0.smul _) (f1.smul _)).trans (add_le_add ?_ ?_))
      ?_
    · rw [gammaNorm_smul hδ f0, abs_of_nonneg (sq_nonneg b)]
    · rw [gammaNorm_smul hδ f1, abs_of_nonneg (by positivity)]
    · rw [gammaNorm_smul hδ f2, abs_of_nonneg hr1]
  refine htri.trans ?_
  -- compare the three coefficient profiles
  have key : b ^ 2 * (1 / a ^ r) + 2 * r * b * (1 / a ^ (r - 1)) +
      r * (r - 1 : ℝ) * (1 / a ^ (r - 2)) ≤ (1 + r) ^ 2 * b ^ 2 / a ^ r := by
    have t2 : 2 * r * b * (1 / a ^ (r - 1)) ≤ 2 * r * (b ^ 2 / a ^ r) := by
      rcases Nat.eq_zero_or_pos r with h0 | hpos
      · subst h0; simp
      · have h := one_div_pow_sub_le ha hab (k := 1) hpos
        rw [pow_one] at h
        calc 2 * r * b * (1 / a ^ (r - 1)) ≤ 2 * r * b * (b / a ^ r) := by gcongr
          _ = _ := by ring
    have t3 : r * (r - 1 : ℝ) * (1 / a ^ (r - 2)) ≤ r * (r - 1 : ℝ) * (b ^ 2 / a ^ r) := by
      rcases lt_or_ge r 2 with h | h
      · interval_cases r <;> simp
      · exact mul_le_mul_of_nonneg_left (one_div_pow_sub_le ha hab h) hr1
    have hsum : (1 + (r : ℝ)) ^ 2 * b ^ 2 / a ^ r = b ^ 2 * (1 / a ^ r) +
        2 * r * (b ^ 2 / a ^ r) + r * (r - 1 : ℝ) * (b ^ 2 / a ^ r) + r * (b ^ 2 / a ^ r) := by
      field_simp
      ring
    have : 0 ≤ (r : ℝ) * (b ^ 2 / a ^ r) := by positivity
    linarith
  calc b ^ 2 * gammaNorm δ (expMono r a) + 2 * r * b * gammaNorm δ (expMono (r - 1) a) +
        r * (r - 1 : ℝ) * gammaNorm δ (expMono (r - 2) a)
      ≤ b ^ 2 * (monoConst r * A / a ^ r) + 2 * r * b * (monoConst r * A / a ^ (r - 1)) +
          r * (r - 1 : ℝ) * (monoConst r * A / a ^ (r - 2)) := by
        gcongr
    _ = monoConst r * A * (b ^ 2 * (1 / a ^ r) + 2 * r * b * (1 / a ^ (r - 1)) +
          r * (r - 1 : ℝ) * (1 / a ^ (r - 2))) := by ring
    _ ≤ monoConst r * A * ((1 + r) ^ 2 * b ^ 2 / a ^ r) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg hK hA0)
    _ = _ := by unfold jetConst; ring

theorem gammaFinite_atomJet {δ : ℝ} (hδ : 0 < 5 + δ) (r : ℕ) {x : ℝ} (hx : 0 < x) :
    GammaFinite δ (atomJet r x) :=
  GammaFinite.of_abs_le (gammaFinite_jetEnvelope hδ r hx x)
    (continuous_atomJet r x).aestronglyMeasurable (fun t ht => by
      refine (abs_atomJet_le hx le_rfl le_rfl ht).trans (le_abs_self _))

/-- **Jet norm law.**  `‖∂_x^r f_x‖_δ ≤ C_r x^(-(5+δ)/2) x^(2-r)`, uniformly in `0 ≤ δ ≤ 1`. -/
theorem gammaNorm_atomJet_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (r : ℕ) {x : ℝ} (hx : 0 < x) :
    gammaNorm δ (atomJet r x) ≤ jetConst r * x ^ 2 * (x ^ ((5 + δ) / 2))⁻¹ / x ^ r := by
  have hδ : 0 < 5 + δ := by linarith
  refine (gammaNorm_le_of_abs_le hδ (gammaFinite_jetEnvelope hδ r hx x)
    (continuous_atomJet r x).aestronglyMeasurable (fun t ht => ?_)).trans
    (gammaNorm_jetEnvelope_le hδ0 hδ1 r hx le_rfl)
  exact (abs_atomJet_le hx le_rfl le_rfl ht).trans (le_abs_self _)

/-! ### Taylor packets -/

/-- The order-`d` Taylor remainder of `b ↦ f_b` expanded at `a`. -/
def taylorRem (d : ℕ) (a b t : ℝ) : ℝ :=
  atom b t - ∑ j ∈ range d, atomJet j a t * (b - a) ^ j / (j.factorial : ℝ)

theorem continuous_taylorRem (d : ℕ) (a b : ℝ) : Continuous (taylorRem d a b) := by
  unfold taylorRem
  refine (continuous_atom b).sub (continuous_finsetSum _ fun j _ => ?_)
  exact ((continuous_atomJet j a).mul continuous_const).div_const _

theorem abs_taylorRem_le {d : ℕ} {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) :
    |taylorRem d a b t| ≤ (b - a) ^ d / (d.factorial : ℝ) * jetEnvelope d a b t := by
  have h := abs_taylor_chain_le (g := fun k x => atomJet k x t)
    (fun k x => hasDerivAt_atomJet k t x) d hab
    (M := jetEnvelope d a b t) (fun y hy => abs_atomJet_le ha hy.1 hy.2 ht)
  unfold taylorRem
  rw [← atomJet_zero]
  calc _ ≤ jetEnvelope d a b t * (b - a) ^ d / (d.factorial : ℝ) := h
    _ = _ := by ring

theorem gammaFinite_taylorRem {δ : ℝ} (hδ : 0 < 5 + δ) (d : ℕ) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) : GammaFinite δ (taylorRem d a b) := by
  unfold taylorRem
  refine GammaFinite.sub (gammaFinite_atom hδ (ha.trans_le hab))
    (GammaFinite.sum _ fun j _ => ?_)
  have h := (gammaFinite_atomJet hδ j ha).smul ((b - a) ^ j / (j.factorial : ℝ))
  refine h.congr ?_
  funext t
  ring

/-- **Taylor remainder law.**  For `0 < a ≤ b` and `0 ≤ δ ≤ 1`,
`‖f_b - Σ_{j<d} (b-a)^j/j! ∂^j f_a‖_δ ≤ (b-a)^d/d! · C_d b² a^(-(5+δ)/2) / a^d`. -/
theorem gammaNorm_taylorRem_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (d : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    gammaNorm δ (taylorRem d a b) ≤
      (b - a) ^ d / (d.factorial : ℝ) * (jetConst d * b ^ 2 * (a ^ ((5 + δ) / 2))⁻¹ / a ^ d) := by
  have hδ : 0 < 5 + δ := by linarith
  have hc : 0 ≤ (b - a) ^ d / (d.factorial : ℝ) := by
    have : 0 ≤ b - a := by linarith
    positivity
  have hfin := (gammaFinite_jetEnvelope hδ d ha b).smul ((b - a) ^ d / (d.factorial : ℝ))
  refine (gammaNorm_le_of_abs_le hδ hfin (continuous_taylorRem d a b).aestronglyMeasurable
    (fun t ht => ?_)).trans ?_
  · refine (abs_taylorRem_le ha hab ht).trans (le_abs_self _)
  · rw [gammaNorm_smul hδ (gammaFinite_jetEnvelope hδ d ha b), abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (gammaNorm_jetEnvelope_le hδ0 hδ1 d ha hab) hc

/-- The exact block Taylor decomposition of a finite atom packet at base point `X`. -/
theorem atomPacket_eq_taylor {ι : Type*} (s : Finset ι) (c p : ι → ℝ) (d : ℕ) (X t : ℝ) :
    ∑ i ∈ s, c i * atom (p i) t =
      ∑ j ∈ range d, (∑ i ∈ s, c i * (p i - X) ^ j) / (j.factorial : ℝ) * atomJet j X t +
        ∑ i ∈ s, c i * taylorRem d X (p i) t := by
  unfold taylorRem
  simp only [mul_sub, sum_sub_distrib, Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm (s := range d) (t := s)]
  have : ∀ i ∈ s, ∑ j ∈ range d, c i * (p i - X) ^ j / (j.factorial : ℝ) * atomJet j X t =
      ∑ j ∈ range d, c i * (atomJet j X t * (p i - X) ^ j / (j.factorial : ℝ)) := by
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  rw [sum_congr rfl this]
  ring

/-- **Block Taylor law.**  A finite signed atom packet whose frequencies lie in `[X, ∞)` is
bounded by its centred moments against the jets at `X`, plus the Taylor remainders. -/
theorem gammaNorm_atomPacket_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {ι : Type*}
    (s : Finset ι) (c p : ι → ℝ) (d : ℕ) {X : ℝ} (hX : 0 < X) (hp : ∀ i ∈ s, X ≤ p i) :
    gammaNorm δ (fun t => ∑ i ∈ s, c i * atom (p i) t) ≤
      ∑ j ∈ range d, |∑ i ∈ s, c i * (p i - X) ^ j| / (j.factorial : ℝ) *
          (jetConst j * X ^ 2 * (X ^ ((5 + δ) / 2))⁻¹ / X ^ j) +
        ∑ i ∈ s, |c i| * ((p i - X) ^ d / (d.factorial : ℝ) *
          (jetConst d * p i ^ 2 * (X ^ ((5 + δ) / 2))⁻¹ / X ^ d)) := by
  have hδ : 0 < 5 + δ := by linarith
  have hJ : ∀ j ∈ range d, GammaFinite δ (fun t =>
      (∑ i ∈ s, c i * (p i - X) ^ j) / (j.factorial : ℝ) * atomJet j X t) := fun j _ =>
    ((gammaFinite_atomJet hδ j hX).smul _)
  have hR : ∀ i ∈ s, GammaFinite δ (fun t => c i * taylorRem d X (p i) t) := fun i hi =>
    (gammaFinite_taylorRem hδ d hX (hp i hi)).smul _
  have heq : (fun t => ∑ i ∈ s, c i * atom (p i) t) = fun t =>
      (∑ j ∈ range d, (∑ i ∈ s, c i * (p i - X) ^ j) / (j.factorial : ℝ) * atomJet j X t) +
        ∑ i ∈ s, c i * taylorRem d X (p i) t := by
    funext t
    exact atomPacket_eq_taylor s c p d X t
  rw [heq]
  refine (gammaNorm_add_le hδ (GammaFinite.sum _ hJ) (GammaFinite.sum _ hR)).trans
    (add_le_add ((gammaNorm_sum_le hδ _ hJ).trans (sum_le_sum fun j _ => ?_))
      ((gammaNorm_sum_le hδ _ hR).trans (sum_le_sum fun i hi => ?_)))
  · rw [gammaNorm_smul hδ (gammaFinite_atomJet hδ j hX), abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < (j.factorial : ℝ))]
    exact mul_le_mul_of_nonneg_left (gammaNorm_atomJet_le hδ0 hδ1 j hX) (by positivity)
  · rw [gammaNorm_smul hδ (gammaFinite_taylorRem hδ d hX (hp i hi))]
    exact mul_le_mul_of_nonneg_left (gammaNorm_taylorRem_le hδ0 hδ1 d hX (hp i hi))
      (abs_nonneg _)

/-! ### Taylor remainders of higher jets -/

/-- The order-`d` Taylor remainder of `b ↦ ∂^r f_b` expanded at `a`. -/
def jetTaylorRem (r d : ℕ) (a b t : ℝ) : ℝ :=
  atomJet r b t - ∑ j ∈ range d, atomJet (r + j) a t * (b - a) ^ j / (j.factorial : ℝ)

theorem continuous_jetTaylorRem (r d : ℕ) (a b : ℝ) : Continuous (jetTaylorRem r d a b) := by
  unfold jetTaylorRem
  refine (continuous_atomJet r b).sub (continuous_finsetSum _ fun j _ => ?_)
  exact ((continuous_atomJet (r + j) a).mul continuous_const).div_const _

theorem abs_jetTaylorRem_le {r d : ℕ} {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) :
    |jetTaylorRem r d a b t| ≤ (b - a) ^ d / (d.factorial : ℝ) * jetEnvelope (r + d) a b t := by
  have h := abs_taylor_chain_le (g := fun k x => atomJet (r + k) x t)
    (fun k x => by simpa [add_assoc] using hasDerivAt_atomJet (r + k) t x) d hab
    (M := jetEnvelope (r + d) a b t) (fun y hy => abs_atomJet_le ha hy.1 hy.2 ht)
  unfold jetTaylorRem
  simp only [add_zero] at h
  calc _ ≤ jetEnvelope (r + d) a b t * (b - a) ^ d / (d.factorial : ℝ) := h
    _ = _ := by ring

theorem gammaFinite_jetTaylorRem {δ : ℝ} (hδ : 0 < 5 + δ) (r d : ℕ) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) : GammaFinite δ (jetTaylorRem r d a b) := by
  unfold jetTaylorRem
  refine GammaFinite.sub (gammaFinite_atomJet hδ r (ha.trans_le hab))
    (GammaFinite.sum _ fun j _ => ?_)
  have h := (gammaFinite_atomJet hδ (r + j) ha).smul ((b - a) ^ j / (j.factorial : ℝ))
  refine h.congr ?_
  funext t
  ring

/-- **Jet Taylor remainder law.**  For `0 < a ≤ b` and `0 ≤ δ ≤ 1`,
`‖∂^r f_b - Σ_{j<d} (b-a)^j/j! ∂^{r+j} f_a‖_δ ≤ (b-a)^d/d! · C_{r+d} b² a^(-(5+δ)/2) / a^(r+d)`. -/
theorem gammaNorm_jetTaylorRem_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (r d : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    gammaNorm δ (jetTaylorRem r d a b) ≤
      (b - a) ^ d / (d.factorial : ℝ) *
        (jetConst (r + d) * b ^ 2 * (a ^ ((5 + δ) / 2))⁻¹ / a ^ (r + d)) := by
  have hδ : 0 < 5 + δ := by linarith
  have hc : 0 ≤ (b - a) ^ d / (d.factorial : ℝ) := by
    have : 0 ≤ b - a := by linarith
    positivity
  have hfin := (gammaFinite_jetEnvelope hδ (r + d) ha b).smul ((b - a) ^ d / (d.factorial : ℝ))
  refine (gammaNorm_le_of_abs_le hδ hfin (continuous_jetTaylorRem r d a b).aestronglyMeasurable
    (fun t ht => ?_)).trans ?_
  · exact (abs_jetTaylorRem_le ha hab ht).trans (le_abs_self _)
  · rw [gammaNorm_smul hδ (gammaFinite_jetEnvelope hδ (r + d) ha b), abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (gammaNorm_jetEnvelope_le hδ0 hδ1 (r + d) ha hab) hc

/-- **Atom Lipschitz law.**  `‖f_b - f_a‖_δ ≤ (b-a) · C_1 b² a^(-(5+δ)/2) / a`. -/
theorem gammaNorm_atom_sub_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    gammaNorm δ (fun t => atom b t - atom a t) ≤
      (b - a) * (jetConst 1 * b ^ 2 * (a ^ ((5 + δ) / 2))⁻¹ / a) := by
  have h := gammaNorm_taylorRem_le hδ0 hδ1 1 ha hab
  have e : taylorRem 1 a b = fun t => atom b t - atom a t := by
    funext t; simp [taylorRem, atomJet_zero]
  rw [e] at h
  simpa using h

end RHTower.CubicGamma
