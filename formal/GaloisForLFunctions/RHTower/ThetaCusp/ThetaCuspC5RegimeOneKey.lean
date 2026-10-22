import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5RegimeOnePerturbation

/-!
# Numeric discharge of the regime-I key inequality

The key inequality of `c5CompletedCompensationMargin_pos_of_regimeOne_key` is reduced, by the
scaling `A(u−t) = 6ρ` (`ρ ≥ 1`) and the decay `ρ^k ε(6ρ) ≤ ε(6)` (`k ≤ 18`), to a one-variable
inequality in `t`, which is verified on twelve chambers of `[1/4, 3]` by monotone bounds and
rational arithmetic, and for `t ≥ 3` by a crude exponential comparison.
-/

open Set

namespace RHTower

namespace C5LikelihoodAffineData

/-- The compensation bound with `e^{-q}` replaced by a free parameter `eq`. -/
noncomputable def boseZeroBoundE (t a' eq : ℝ) : ℝ := 14 + 10 * t * a' + 16 * t * a' * eq
noncomputable def boseDiffBoundE (t a' da' dq' eq : ℝ) : ℝ :=
  10 * t * da' + 48 * t * da' * eq + 192 * t * a' * dq' * eq
noncomputable def compensationDiffBoundE (t a' b' c' s' m' n' da' db' dc' ds' dm' dn' dq' eq : ℝ) : ℝ :=
  5 * slopeDiffBound t a' b' c' s' m' n' da' db' dc' ds' dm' dn' +
    boseDiffBoundE t a' da' dq' eq *
      (centerZeroBound t a' b' s' m' + centerDiffBound t a' b' s' m' da' db' ds' dm') +
    boseZeroBoundE t a' eq * centerDiffBound t a' b' s' m' da' db' ds' dm'

theorem compensationDiffBound_eq_E (t a' b' c' s' m' n' da' db' dc' ds' dm' dn' dq' q : ℝ) :
    compensationDiffBound t a' b' c' s' m' n' da' db' dc' ds' dm' dn' dq' q =
      compensationDiffBoundE t a' b' c' s' m' n' da' db' dc' ds' dm' dn' dq' (Real.exp (-q)) := rfl

/-- Monotonicity of the bound in all its (nonnegative) arguments. -/
theorem compensationDiffBoundE_mono {t a' b' c' s' m' n' da' db' dc' ds' dm' dn' dq' eq : ℝ}
    {a'' b'' c'' s'' m'' n'' da'' db'' dc'' ds'' dm'' dn'' dq'' eq' : ℝ}
    (ht : 0 ≤ t) (ha : 0 ≤ a') (hb : 0 ≤ b') (hc : 0 ≤ c') (hs : 0 ≤ s') (hm : 0 ≤ m') (hn : 0 ≤ n')
    (hda : 0 ≤ da') (hdb : 0 ≤ db') (hdc : 0 ≤ dc') (hds : 0 ≤ ds') (hdm : 0 ≤ dm') (hdn : 0 ≤ dn')
    (hdq : 0 ≤ dq') (heq : 0 ≤ eq)
    (ha' : a' ≤ a'') (hb' : b' ≤ b'') (hc' : c' ≤ c'') (hs' : s' ≤ s'') (hm' : m' ≤ m'') (hn' : n' ≤ n'')
    (hda' : da' ≤ da'') (hdb' : db' ≤ db'') (hdc' : dc' ≤ dc'') (hds' : ds' ≤ ds'') (hdm' : dm' ≤ dm'')
    (hdn' : dn' ≤ dn'') (hdq' : dq' ≤ dq'') (heq' : eq ≤ eq') :
    compensationDiffBoundE t a' b' c' s' m' n' da' db' dc' ds' dm' dn' dq' eq ≤
      compensationDiffBoundE t a'' b'' c'' s'' m'' n'' da'' db'' dc'' ds'' dm'' dn'' dq'' eq' := by
  unfold compensationDiffBoundE slopeDiffBound centerZeroBound centerDiffBound boseZeroBoundE
    boseDiffBoundE
  have ht2 : 0 ≤ t ^ (2 : ℕ) := by positivity
  have ha2 : 0 ≤ a'' := le_trans ha ha'
  have hb2 : 0 ≤ b'' := le_trans hb hb'
  have hc2 : 0 ≤ c'' := le_trans hc hc'
  have hs2 : 0 ≤ s'' := le_trans hs hs'
  have hm2 : 0 ≤ m'' := le_trans hm hm'
  have hn2 : 0 ≤ n'' := le_trans hn hn'
  have hda2 : 0 ≤ da'' := le_trans hda hda'
  have hdb2 : 0 ≤ db'' := le_trans hdb hdb'
  have hdc2 : 0 ≤ dc'' := le_trans hdc hdc'
  have hds2 : 0 ≤ ds'' := le_trans hds hds'
  have hdm2 : 0 ≤ dm'' := le_trans hdm hdm'
  have hdn2 : 0 ≤ dn'' := le_trans hdn hdn'
  have hdq2 : 0 ≤ dq'' := le_trans hdq hdq'
  have heq2 : 0 ≤ eq' := le_trans heq heq'
  gcongr <;> positivity

end C5LikelihoodAffineData

/-! ## Exponential numerics -/

theorem exp_half_bounds : (1.6487211 : ℝ) ≤ Real.exp (1 / 2) ∧ Real.exp (1 / 2) ≤ 1.6487213 := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2) 8
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  · have h := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num) (by norm_num : 0 < 8)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith

theorem exp_threeFifths_bounds : (1.8221183 : ℝ) ≤ Real.exp (3 / 5) ∧ Real.exp (3 / 5) ≤ 1.8221189 := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3 / 5) 8
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  · have h := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 3 / 5) (by norm_num) (by norm_num : 0 < 8)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith

theorem exp_sevenTenths_bounds : (2.0137511 : ℝ) ≤ Real.exp (7 / 10) ∧ Real.exp (7 / 10) ≤ 2.0137528 := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 7 / 10) 8
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  · have h := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 7 / 10) (by norm_num) (by norm_num : 0 < 8)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith

theorem exp_fourFifths_bounds : (2.2255363 : ℝ) ≤ Real.exp (4 / 5) ∧ Real.exp (4 / 5) ≤ 2.2255411 := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 4 / 5) 8
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  · have h := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 4 / 5) (by norm_num) (by norm_num : 0 < 8)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith

theorem exp_one_bounds : (2.7182818283 : ℝ) ≤ Real.exp 1 ∧ Real.exp 1 ≤ 2.7182818286 :=
  ⟨Real.exp_one_gt_d9.le, Real.exp_one_lt_d9.le⟩

/-- Products of the basic bounds. -/
theorem exp_mul_bounds {x y lx ux ly uy : ℝ} (hx : lx ≤ Real.exp x ∧ Real.exp x ≤ ux)
    (hy : ly ≤ Real.exp y ∧ Real.exp y ≤ uy) (hlx : 0 ≤ lx) (hly : 0 ≤ ly) :
    lx * ly ≤ Real.exp (x + y) ∧ Real.exp (x + y) ≤ ux * uy := by
  rw [Real.exp_add]
  exact ⟨mul_le_mul hx.1 hy.1 hly (Real.exp_pos _).le,
    mul_le_mul hx.2 hy.2 (Real.exp_pos _).le (le_trans (Real.exp_pos x).le hx.2)⟩

/-! ## The one-variable key -/

/-- Left side of the key at scale `ρ = 1`, as a function of `w = e^{2t}`, `winv = 1/w`,
`z = cosh 2t − 1`, `zp = 2 sinh 2t`, `t`, the scale `ε` and `eq ≥ e^{-q}`. -/
noncomputable def keyLHS (ε w winv z zp t eq : ℝ) : ℝ :=
  C5LikelihoodAffineData.compensationDiffBoundE t ((12 * w + 2 * winv) * zp)
    (4 * (2 * winv) ^ (2 : ℕ) * z * (z + 2) + 4 * (12 * w + 2 * winv) * (z + 1))
    (zp * (8 * (2 * winv) ^ (3 : ℕ) * z * (z + 2) + 12 * (2 * winv) ^ (2 : ℕ) * (z + 1) + 4 * (12 * w + 2 * winv)))
    (24 * w * z + 6 * z * winv) ((24 * w + 12 * winv) * zp)
    (4 * (48 * winv ^ (2 : ℕ) * z * (z + 2) + (24 * w + 12 * winv) * (z + 1)))
    (72 * ε) (2736 * ε) (112752 * ε) (144 * ε) (2736 * ε) (112752 * ε) (4 * ε) eq

/-- Right side of the key at scale `ρ = 1`. -/
noncomputable def keyRHS (w t : ℝ) : ℝ :=
  (288 * w ^ (2 : ℕ) - 72) * (6656 / 9 * t ^ (7 : ℕ) + 615872 / 945 * t ^ (9 : ℕ) + 50560 / 189 * t ^ (11 : ℕ))

/-- Monotonicity of `keyLHS` in all arguments. -/
theorem keyLHS_mono {ε w winv z zp t eq εb wb winvb zb zpb tb eqb : ℝ}
    (hε0 : 0 ≤ ε) (hw0 : 0 ≤ w) (hwinv0 : 0 ≤ winv) (hz0 : 0 ≤ z) (hzp0 : 0 ≤ zp) (ht0 : 0 ≤ t)
    (heq0 : 0 ≤ eq)
    (hε : ε ≤ εb) (hw : w ≤ wb) (hwinv : winv ≤ winvb) (hz : z ≤ zb) (hzp : zp ≤ zpb) (ht : t ≤ tb)
    (heq : eq ≤ eqb) :
    keyLHS ε w winv z zp t eq ≤ keyLHS εb wb winvb zb zpb tb eqb := by
  unfold keyLHS
  have hwb0 : 0 ≤ wb := le_trans hw0 hw
  have hwinvb0 : 0 ≤ winvb := le_trans hwinv0 hwinv
  have hzb0 : 0 ≤ zb := le_trans hz0 hz
  have hzpb0 : 0 ≤ zpb := le_trans hzp0 hzp
  -- the bound is monotone in `t` as well, through `compensationDiffBoundE`'s explicit `t`
  -- dependence; we separate the two monotonicities.
  have step1 := C5LikelihoodAffineData.compensationDiffBoundE_mono (t := t)
    (a' := (12 * w + 2 * winv) * zp) (b' := 4 * (2 * winv) ^ (2 : ℕ) * z * (z + 2) + 4 * (12 * w + 2 * winv) * (z + 1))
    (c' := zp * (8 * (2 * winv) ^ (3 : ℕ) * z * (z + 2) + 12 * (2 * winv) ^ (2 : ℕ) * (z + 1) + 4 * (12 * w + 2 * winv)))
    (s' := 24 * w * z + 6 * z * winv) (m' := (24 * w + 12 * winv) * zp)
    (n' := 4 * (48 * winv ^ (2 : ℕ) * z * (z + 2) + (24 * w + 12 * winv) * (z + 1)))
    (da' := 72 * ε) (db' := 2736 * ε) (dc' := 112752 * ε) (ds' := 144 * ε) (dm' := 2736 * ε)
    (dn' := 112752 * ε) (dq' := 4 * ε) (eq := eq)
    (a'' := (12 * wb + 2 * winvb) * zpb)
    (b'' := 4 * (2 * winvb) ^ (2 : ℕ) * zb * (zb + 2) + 4 * (12 * wb + 2 * winvb) * (zb + 1))
    (c'' := zpb * (8 * (2 * winvb) ^ (3 : ℕ) * zb * (zb + 2) + 12 * (2 * winvb) ^ (2 : ℕ) * (zb + 1) + 4 * (12 * wb + 2 * winvb)))
    (s'' := 24 * wb * zb + 6 * zb * winvb) (m'' := (24 * wb + 12 * winvb) * zpb)
    (n'' := 4 * (48 * winvb ^ (2 : ℕ) * zb * (zb + 2) + (24 * wb + 12 * winvb) * (zb + 1)))
    (da'' := 72 * εb) (db'' := 2736 * εb) (dc'' := 112752 * εb) (ds'' := 144 * εb) (dm'' := 2736 * εb)
    (dn'' := 112752 * εb) (dq'' := 4 * εb) (eq' := eqb)
    ht0 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) heq0
    (by gcongr) (by gcongr) (by gcongr) (by gcongr) (by gcongr) (by gcongr)
    (by gcongr) (by gcongr) (by gcongr) (by gcongr) (by gcongr) (by gcongr) (by gcongr) heq
  -- monotonicity in `t`
  have step2 : C5LikelihoodAffineData.compensationDiffBoundE t ((12 * wb + 2 * winvb) * zpb)
      (4 * (2 * winvb) ^ (2 : ℕ) * zb * (zb + 2) + 4 * (12 * wb + 2 * winvb) * (zb + 1))
      (zpb * (8 * (2 * winvb) ^ (3 : ℕ) * zb * (zb + 2) + 12 * (2 * winvb) ^ (2 : ℕ) * (zb + 1) + 4 * (12 * wb + 2 * winvb)))
      (24 * wb * zb + 6 * zb * winvb) ((24 * wb + 12 * winvb) * zpb)
      (4 * (48 * winvb ^ (2 : ℕ) * zb * (zb + 2) + (24 * wb + 12 * winvb) * (zb + 1)))
      (72 * εb) (2736 * εb) (112752 * εb) (144 * εb) (2736 * εb) (112752 * εb) (4 * εb) eqb ≤
      C5LikelihoodAffineData.compensationDiffBoundE tb ((12 * wb + 2 * winvb) * zpb)
      (4 * (2 * winvb) ^ (2 : ℕ) * zb * (zb + 2) + 4 * (12 * wb + 2 * winvb) * (zb + 1))
      (zpb * (8 * (2 * winvb) ^ (3 : ℕ) * zb * (zb + 2) + 12 * (2 * winvb) ^ (2 : ℕ) * (zb + 1) + 4 * (12 * wb + 2 * winvb)))
      (24 * wb * zb + 6 * zb * winvb) ((24 * wb + 12 * winvb) * zpb)
      (4 * (48 * winvb ^ (2 : ℕ) * zb * (zb + 2) + (24 * wb + 12 * winvb) * (zb + 1)))
      (72 * εb) (2736 * εb) (112752 * εb) (144 * εb) (2736 * εb) (112752 * εb) (4 * εb) eqb := by
    unfold C5LikelihoodAffineData.compensationDiffBoundE C5LikelihoodAffineData.slopeDiffBound
      C5LikelihoodAffineData.centerZeroBound C5LikelihoodAffineData.centerDiffBound
      C5LikelihoodAffineData.boseZeroBoundE C5LikelihoodAffineData.boseDiffBoundE
    have hεb0 : 0 ≤ εb := le_trans hε0 hε
    have heqb0 : 0 ≤ eqb := le_trans heq0 heq
    have htb0 : 0 ≤ tb := le_trans ht0 ht
    gcongr <;> positivity
  exact step1.trans step2

theorem keyRHS_mono {w t wa ta : ℝ} (hwa1 : 1 ≤ wa) (hw : wa ≤ w) (hta0 : 0 ≤ ta) (ht : ta ≤ t) :
    keyRHS wa ta ≤ keyRHS w t := by
  unfold keyRHS
  have hw0 : 0 ≤ wa := by linarith
  have hpoly : 6656 / 9 * ta ^ (7 : ℕ) + 615872 / 945 * ta ^ (9 : ℕ) + 50560 / 189 * ta ^ (11 : ℕ) ≤
      6656 / 9 * t ^ (7 : ℕ) + 615872 / 945 * t ^ (9 : ℕ) + 50560 / 189 * t ^ (11 : ℕ) := by gcongr
  have hsq : wa ^ (2 : ℕ) ≤ w ^ (2 : ℕ) := pow_le_pow_left₀ hw0 hw 2
  have hfac : 288 * wa ^ (2 : ℕ) - 72 ≤ 288 * w ^ (2 : ℕ) - 72 := by linarith
  have h1 : 0 ≤ 288 * wa ^ (2 : ℕ) - 72 := by nlinarith
  exact mul_le_mul hfac hpoly (by positivity) (by linarith)

/-- Chamber transfer: if the corner values satisfy the strict inequality, so do all interior
points. -/
theorem key_of_chamber {ε w winv z zp t eq εb wa wb winvb zb zpb ta tb eqb : ℝ}
    (hε0 : 0 ≤ ε) (hw0 : 0 ≤ w) (hwinv0 : 0 ≤ winv) (hz0 : 0 ≤ z) (hzp0 : 0 ≤ zp) (ht0 : 0 ≤ ta)
    (heq0 : 0 ≤ eq) (hwa1 : 1 ≤ wa)
    (hε : ε ≤ εb) (hwa : wa ≤ w) (hw : w ≤ wb) (hwinv : winv ≤ winvb) (hz : z ≤ zb) (hzp : zp ≤ zpb)
    (hta : ta ≤ t) (ht : t ≤ tb) (heq : eq ≤ eqb)
    (hnum : keyLHS εb wb winvb zb zpb tb eqb < keyRHS wa ta) :
    keyLHS ε w winv z zp t eq < keyRHS w t :=
  lt_of_le_of_lt (keyLHS_mono hε0 hw0 hwinv0 hz0 hzp0 (le_trans ht0 hta) heq0 hε hw hwinv hz hzp ht heq)
    (lt_of_lt_of_le hnum (keyRHS_mono hwa1 hwa ht0 hta))

/-- `w ↦ (w + 1/w)/2 − 1` and `w ↦ w − 1/w` are monotone for `w ≥ 1`. -/
theorem defect_le_of_le {w wb : ℝ} (hw1 : 1 ≤ w) (hw : w ≤ wb) :
    (w + 1 / w) / 2 - 1 ≤ (wb + 1 / wb) / 2 - 1 ∧ w - 1 / w ≤ wb - 1 / wb := by
  have hw0 : 0 < w := by linarith
  have hwb1 : 1 ≤ wb := le_trans hw1 hw
  have hwb0 : 0 < wb := by linarith
  have hinv : 1 / wb ≤ 1 / w := one_div_le_one_div_of_le hw0 hw
  have hprod : 1 / w - 1 / wb ≤ wb - w := by
    have e : 1 / w - 1 / wb = (wb - w) / (w * wb) := by field_simp
    rw [e]
    exact div_le_self (by linarith) (one_le_mul_of_one_le_of_one_le hw1 hwb1)
  constructor <;> linarith

/-! ## Scaling: absorbing `A(u−t) = 6ρ` -/

namespace C5LikelihoodAffineData

theorem slopeDiffBound_scale {ρ t a' b' c' s' m' n' da' db' dc' ds' dm' dn' : ℝ} (hρ : 1 ≤ ρ)
    (ht : 0 ≤ t) (ha : 0 ≤ a') (hb : 0 ≤ b') (hc : 0 ≤ c') (hs : 0 ≤ s') (hm : 0 ≤ m') (hn : 0 ≤ n')
    (hda : 0 ≤ da') (hdb : 0 ≤ db') (hdc : 0 ≤ dc') (hds : 0 ≤ ds') (hdm : 0 ≤ dm') (hdn : 0 ≤ dn') :
    slopeDiffBound t (ρ ^ (3 : ℕ) * a') (ρ ^ (3 : ℕ) * b') (ρ ^ (3 : ℕ) * c') (ρ ^ (3 : ℕ) * s') (ρ ^ (3 : ℕ) * m') (ρ ^ (3 : ℕ) * n')
      (da' / ρ ^ (9 : ℕ)) (db' / ρ ^ (9 : ℕ)) (dc' / ρ ^ (9 : ℕ)) (ds' / ρ ^ (9 : ℕ)) (dm' / ρ ^ (9 : ℕ)) (dn' / ρ ^ (9 : ℕ)) ≤
    slopeDiffBound t a' b' c' s' m' n' da' db' dc' ds' dm' dn' := by
  have hρ0 : 0 < ρ := by linarith
  have hρ6 : (1 : ℝ) ≤ ρ ^ (6 : ℕ) := one_le_pow₀ hρ
  have hρ18 : (1 : ℝ) ≤ ρ ^ (18 : ℕ) := one_le_pow₀ hρ
  unfold slopeDiffBound
  have e : da' / ρ ^ (9 : ℕ) * (t * (ρ ^ (3 : ℕ) * m') + t ^ (2 : ℕ) * (ρ ^ (3 : ℕ) * n')) +
      ρ ^ (3 : ℕ) * a' * (t * (dm' / ρ ^ (9 : ℕ)) + t ^ (2 : ℕ) * (dn' / ρ ^ (9 : ℕ))) +
      (da' / ρ ^ (9 : ℕ) + 3 * t * (db' / ρ ^ (9 : ℕ)) + t ^ (2 : ℕ) * (dc' / ρ ^ (9 : ℕ))) * (ρ ^ (3 : ℕ) * s') +
      (ρ ^ (3 : ℕ) * a' + 3 * t * (ρ ^ (3 : ℕ) * b') + t ^ (2 : ℕ) * (ρ ^ (3 : ℕ) * c')) * (ds' / ρ ^ (9 : ℕ)) +
      (da' / ρ ^ (9 : ℕ) * (t * (dm' / ρ ^ (9 : ℕ)) + t ^ (2 : ℕ) * (dn' / ρ ^ (9 : ℕ))) +
        (da' / ρ ^ (9 : ℕ) + 3 * t * (db' / ρ ^ (9 : ℕ)) + t ^ (2 : ℕ) * (dc' / ρ ^ (9 : ℕ))) * (ds' / ρ ^ (9 : ℕ))) =
      (da' * (t * m' + t ^ (2 : ℕ) * n') + a' * (t * dm' + t ^ (2 : ℕ) * dn') +
        (da' + 3 * t * db' + t ^ (2 : ℕ) * dc') * s' + (a' + 3 * t * b' + t ^ (2 : ℕ) * c') * ds') / ρ ^ (6 : ℕ) +
      (da' * (t * dm' + t ^ (2 : ℕ) * dn') + (da' + 3 * t * db' + t ^ (2 : ℕ) * dc') * ds') / ρ ^ (18 : ℕ) := by
    field_simp
    try ring
  rw [e]
  have h1 : 0 ≤ da' * (t * m' + t ^ (2 : ℕ) * n') + a' * (t * dm' + t ^ (2 : ℕ) * dn') +
      (da' + 3 * t * db' + t ^ (2 : ℕ) * dc') * s' + (a' + 3 * t * b' + t ^ (2 : ℕ) * c') * ds' := by positivity
  have h2 : 0 ≤ da' * (t * dm' + t ^ (2 : ℕ) * dn') + (da' + 3 * t * db' + t ^ (2 : ℕ) * dc') * ds' := by positivity
  have := div_le_self h1 hρ6
  have := div_le_self h2 hρ18
  linarith

theorem centerDiffBound_scale {ρ t a' b' s' m' da' db' ds' dm' : ℝ} (hρ : 1 ≤ ρ)
    (ht : 0 ≤ t) (ha : 0 ≤ a') (hb : 0 ≤ b') (hs : 0 ≤ s') (hm : 0 ≤ m')
    (hda : 0 ≤ da') (hdb : 0 ≤ db') (hds : 0 ≤ ds') (hdm : 0 ≤ dm') :
    centerDiffBound t (ρ ^ (3 : ℕ) * a') (ρ ^ (3 : ℕ) * b') (ρ ^ (3 : ℕ) * s') (ρ ^ (3 : ℕ) * m')
      (da' / ρ ^ (9 : ℕ)) (db' / ρ ^ (9 : ℕ)) (ds' / ρ ^ (9 : ℕ)) (dm' / ρ ^ (9 : ℕ)) ≤
    centerDiffBound t a' b' s' m' da' db' ds' dm' / ρ ^ (6 : ℕ) := by
  have hρ0 : 0 < ρ := by linarith
  have hρ6 : 0 < ρ ^ (6 : ℕ) := by positivity
  have hρ12 : (1 : ℝ) ≤ ρ ^ (12 : ℕ) := one_le_pow₀ hρ
  unfold centerDiffBound
  have e : da' / ρ ^ (9 : ℕ) * (t * (ρ ^ (3 : ℕ) * m')) + ρ ^ (3 : ℕ) * a' * (t * (dm' / ρ ^ (9 : ℕ))) +
      (da' / ρ ^ (9 : ℕ) + t * (db' / ρ ^ (9 : ℕ))) * (ρ ^ (3 : ℕ) * s') + (ρ ^ (3 : ℕ) * a' + t * (ρ ^ (3 : ℕ) * b')) * (ds' / ρ ^ (9 : ℕ)) +
      (da' / ρ ^ (9 : ℕ) * (t * (dm' / ρ ^ (9 : ℕ))) + (da' / ρ ^ (9 : ℕ) + t * (db' / ρ ^ (9 : ℕ))) * (ds' / ρ ^ (9 : ℕ))) =
      (da' * (t * m') + a' * (t * dm') + (da' + t * db') * s' + (a' + t * b') * ds') / ρ ^ (6 : ℕ) +
      (da' * (t * dm') + (da' + t * db') * ds') / ρ ^ (6 : ℕ) / ρ ^ (12 : ℕ) := by
    field_simp
    try ring
  rw [e]
  have h2' : 0 ≤ (da' * (t * dm') + (da' + t * db') * ds') / ρ ^ (6 : ℕ) := by positivity
  have hd := div_le_self h2' hρ12
  have hsum := add_div (da' * (t * m') + a' * (t * dm') + (da' + t * db') * s' + (a' + t * b') * ds')
    (da' * (t * dm') + (da' + t * db') * ds') (ρ ^ (6 : ℕ))
  linarith

theorem centerZeroBound_scale (ρ t a' b' s' m' : ℝ) :
    centerZeroBound t (ρ ^ (3 : ℕ) * a') (ρ ^ (3 : ℕ) * b') (ρ ^ (3 : ℕ) * s') (ρ ^ (3 : ℕ) * m') =
      ρ ^ (6 : ℕ) * centerZeroBound t a' b' s' m' := by
  unfold centerZeroBound
  ring

theorem boseZeroBoundE_scale {ρ t a' eq : ℝ} (hρ : 1 ≤ ρ) (ht : 0 ≤ t) (ha : 0 ≤ a') (heq : 0 ≤ eq) :
    boseZeroBoundE t (ρ ^ (3 : ℕ) * a') eq ≤ ρ ^ (3 : ℕ) * boseZeroBoundE t a' eq := by
  unfold boseZeroBoundE
  have hρ3 : (1 : ℝ) ≤ ρ ^ (3 : ℕ) := one_le_pow₀ hρ
  nlinarith [mul_nonneg ht ha, mul_nonneg (mul_nonneg ht ha) heq]

theorem boseDiffBoundE_scale {ρ t a' da' dq' eq : ℝ} (hρ : 1 ≤ ρ) (ht : 0 ≤ t) (ha : 0 ≤ a')
    (hda : 0 ≤ da') (hdq : 0 ≤ dq') (heq : 0 ≤ eq) :
    boseDiffBoundE t (ρ ^ (3 : ℕ) * a') (da' / ρ ^ (9 : ℕ)) (dq' / ρ ^ (9 : ℕ)) eq ≤ boseDiffBoundE t a' da' dq' eq / ρ ^ (6 : ℕ) := by
  have hρ0 : 0 < ρ := by linarith
  have hρ3 : (1 : ℝ) ≤ ρ ^ (3 : ℕ) := one_le_pow₀ hρ
  unfold boseDiffBoundE
  have e : 10 * t * (da' / ρ ^ (9 : ℕ)) + 48 * t * (da' / ρ ^ (9 : ℕ)) * eq + 192 * t * (ρ ^ (3 : ℕ) * a') * (dq' / ρ ^ (9 : ℕ)) * eq =
      (10 * t * da' + 48 * t * da' * eq) / ρ ^ (6 : ℕ) / ρ ^ (3 : ℕ) + 192 * t * a' * dq' * eq / ρ ^ (6 : ℕ) := by
    field_simp
    try ring
  rw [e]
  have h1 : 0 ≤ (10 * t * da' + 48 * t * da' * eq) / ρ ^ (6 : ℕ) := by positivity
  have hd := div_le_self h1 hρ3
  have hsum := add_div (10 * t * da' + 48 * t * da' * eq) (192 * t * a' * dq' * eq) (ρ ^ (6 : ℕ))
  linarith

/-- **Scaling lemma.** -/
theorem compensationDiffBoundE_scale {ρ t a' b' c' s' m' n' da' db' dc' ds' dm' dn' dq' eq : ℝ}
    (hρ : 1 ≤ ρ) (ht : 0 ≤ t) (ha : 0 ≤ a') (hb : 0 ≤ b') (hc : 0 ≤ c') (hs : 0 ≤ s') (hm : 0 ≤ m')
    (hn : 0 ≤ n') (hda : 0 ≤ da') (hdb : 0 ≤ db') (hdc : 0 ≤ dc') (hds : 0 ≤ ds') (hdm : 0 ≤ dm')
    (hdn : 0 ≤ dn') (hdq : 0 ≤ dq') (heq : 0 ≤ eq) :
    compensationDiffBoundE t (ρ ^ (3 : ℕ) * a') (ρ ^ (3 : ℕ) * b') (ρ ^ (3 : ℕ) * c') (ρ ^ (3 : ℕ) * s') (ρ ^ (3 : ℕ) * m') (ρ ^ (3 : ℕ) * n')
      (da' / ρ ^ (9 : ℕ)) (db' / ρ ^ (9 : ℕ)) (dc' / ρ ^ (9 : ℕ)) (ds' / ρ ^ (9 : ℕ)) (dm' / ρ ^ (9 : ℕ)) (dn' / ρ ^ (9 : ℕ)) (dq' / ρ ^ (9 : ℕ)) eq ≤
    compensationDiffBoundE t a' b' c' s' m' n' da' db' dc' ds' dm' dn' dq' eq := by
  have hρ0 : 0 < ρ := by linarith
  have hρ3 : (1 : ℝ) ≤ ρ ^ (3 : ℕ) := one_le_pow₀ hρ
  have hρ6 : (1 : ℝ) ≤ ρ ^ (6 : ℕ) := one_le_pow₀ hρ
  have hρ12 : (1 : ℝ) ≤ ρ ^ (12 : ℕ) := one_le_pow₀ hρ
  unfold compensationDiffBoundE
  have hS := slopeDiffBound_scale hρ ht ha hb hc hs hm hn hda hdb hdc hds hdm hdn
  have hC := centerDiffBound_scale hρ ht ha hb hs hm hda hdb hds hdm
  have hZ := centerZeroBound_scale ρ t a' b' s' m'
  have hW0 := boseZeroBoundE_scale hρ ht ha heq
  have hWd := boseDiffBoundE_scale hρ ht ha hda hdq heq
  -- nonnegativity of the pieces
  have hC0 : 0 ≤ centerDiffBound t (ρ ^ (3 : ℕ) * a') (ρ ^ (3 : ℕ) * b') (ρ ^ (3 : ℕ) * s') (ρ ^ (3 : ℕ) * m')
      (da' / ρ ^ (9 : ℕ)) (db' / ρ ^ (9 : ℕ)) (ds' / ρ ^ (9 : ℕ)) (dm' / ρ ^ (9 : ℕ)) := by
    unfold centerDiffBound; positivity
  have hCu : 0 ≤ centerDiffBound t a' b' s' m' da' db' ds' dm' := by
    unfold centerDiffBound; positivity
  have hZu : 0 ≤ centerZeroBound t a' b' s' m' := by
    unfold centerZeroBound; positivity
  have hWd0 : 0 ≤ boseDiffBoundE t (ρ ^ (3 : ℕ) * a') (da' / ρ ^ (9 : ℕ)) (dq' / ρ ^ (9 : ℕ)) eq := by
    unfold boseDiffBoundE; positivity
  have hWdu : 0 ≤ boseDiffBoundE t a' da' dq' eq := by
    unfold boseDiffBoundE; positivity
  have hW0u : 0 ≤ boseZeroBoundE t a' eq := by
    unfold boseZeroBoundE; positivity
  have hW00 : 0 ≤ boseZeroBoundE t (ρ ^ (3 : ℕ) * a') eq := by
    unfold boseZeroBoundE; positivity
  set Cs := centerDiffBound t (ρ ^ (3 : ℕ) * a') (ρ ^ (3 : ℕ) * b') (ρ ^ (3 : ℕ) * s') (ρ ^ (3 : ℕ) * m')
      (da' / ρ ^ (9 : ℕ)) (db' / ρ ^ (9 : ℕ)) (ds' / ρ ^ (9 : ℕ)) (dm' / ρ ^ (9 : ℕ))
  set Cu := centerDiffBound t a' b' s' m' da' db' ds' dm'
  set Zu := centerZeroBound t a' b' s' m'
  set Wds := boseDiffBoundE t (ρ ^ (3 : ℕ) * a') (da' / ρ ^ (9 : ℕ)) (dq' / ρ ^ (9 : ℕ)) eq
  set Wdu := boseDiffBoundE t a' da' dq' eq
  set W0s := boseZeroBoundE t (ρ ^ (3 : ℕ) * a') eq
  set W0u := boseZeroBoundE t a' eq
  rw [hZ]
  -- second term: `Wds (ρ⁶ Zu + Cs) ≤ (Wdu/ρ⁶)(ρ⁶ Zu + Cu/ρ⁶) = Wdu Zu + Wdu Cu/ρ¹²`
  have t2 : Wds * (ρ ^ (6 : ℕ) * Zu + Cs) ≤ Wdu * Zu + Wdu * Cu / ρ ^ (12 : ℕ) := by
    have h := mul_le_mul hWd (add_le_add_left hC (ρ ^ (6 : ℕ) * Zu)) (by positivity) (by positivity)
    have e : Wdu / ρ ^ (6 : ℕ) * (ρ ^ (6 : ℕ) * Zu + Cu / ρ ^ (6 : ℕ)) = Wdu * Zu + Wdu * Cu / ρ ^ (12 : ℕ) := by
      field_simp
      try ring
    linarith
  -- third term: `W0s Cs ≤ ρ³ W0u Cu/ρ⁶ = W0u Cu / ρ³`
  have t3 : W0s * Cs ≤ W0u * Cu / ρ ^ (3 : ℕ) := by
    have h := mul_le_mul hW0 hC hC0 (by positivity)
    have e : ρ ^ (3 : ℕ) * W0u * (Cu / ρ ^ (6 : ℕ)) = W0u * Cu / ρ ^ (3 : ℕ) := by
      field_simp
      try ring
    linarith
  have d1 : Wdu * Cu / ρ ^ (12 : ℕ) ≤ Wdu * Cu := div_le_self (by positivity) hρ12
  have d2 : W0u * Cu / ρ ^ (3 : ℕ) ≤ W0u * Cu := div_le_self (by positivity) hρ3
  linarith

end C5LikelihoodAffineData

/-! ## Chamber numerics -/

/-- Chamber `[1/4, 3/10]`. -/
theorem key_chamber_1 :
    keyLHS (49 / 100000000) 1.8221189 (1 / 1.6487211) ((1.8221189 + 1 / 1.8221189) / 2 - 1)
        (1.8221189 - 1 / 1.8221189) (3 / 10)
        (1 / (1 + 12 * 1.6487211 * ((1.6487211 + 1 / 1.6487211) / 2 - 1))) <
      keyRHS 1.6487211 (1 / 4) := by
  unfold keyLHS keyRHS C5LikelihoodAffineData.compensationDiffBoundE C5LikelihoodAffineData.slopeDiffBound
    C5LikelihoodAffineData.centerZeroBound C5LikelihoodAffineData.centerDiffBound
    C5LikelihoodAffineData.boseZeroBoundE C5LikelihoodAffineData.boseDiffBoundE
  norm_num

/-! ## Endpoint exponential bounds and the remaining chambers -/

theorem exp_sixFifths_bounds : (3.32011509919489 : ℝ) ≤ Real.exp (6/5) ∧ Real.exp (6/5) ≤ 3.32011728573721 := by
  have h := exp_mul_bounds exp_threeFifths_bounds exp_threeFifths_bounds (by norm_num) (by norm_num)
  rw [show (6/5 : ℝ) = 3/5 + 3/5 by norm_num]
  constructor
  · linarith [h.1]
  · linarith [h.2]

theorem exp_threeHalves_bounds : (4.48168860606478713 : ℝ) ≤ Real.exp (3/2) ∧ Real.exp (3/2) ≤ 4.48168915021576918 := by
  have h := exp_mul_bounds exp_one_bounds exp_half_bounds (by norm_num) (by norm_num)
  rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num]
  constructor
  · linarith [h.1]
  · linarith [h.2]

theorem exp_two_bounds : (7.38905609806599068089 : ℝ) ≤ Real.exp (2) ∧ Real.exp (2) ≤ 7.38905609969695977796 := by
  have h := exp_mul_bounds exp_one_bounds exp_one_bounds (by norm_num) (by norm_num)
  rw [show (2 : ℝ) = 1 + 1 by norm_num]
  constructor
  · linarith [h.1]
  · linarith [h.2]

theorem exp_fiveHalves_bounds : (12.182492697965068027986709779 : ℝ) ≤ Real.exp (5/2) ∧ Real.exp (5/2) ≤ 12.182494178465301131165922548 := by
  have h := exp_mul_bounds exp_two_bounds exp_half_bounds (by norm_num) (by norm_num)
  rw [show (5/2 : ℝ) = 2 + 1/2 by norm_num]
  constructor
  · linarith [h.1]
  · linarith [h.2]

theorem exp_three_bounds : (20.085536919662085242100431071187 : ℝ) ≤ Real.exp (3) ∧ Real.exp (3) ≤ 20.085536926312235731093758777656 := by
  have h := exp_mul_bounds exp_two_bounds exp_one_bounds (by norm_num) (by norm_num)
  rw [show (3 : ℝ) = 2 + 1 by norm_num]
  constructor
  · linarith [h.1]
  · linarith [h.2]

theorem exp_four_bounds : (54.5981500203662032900872079044043258111921 : ℝ) ≤ Real.exp (4) ∧ Real.exp (4) ≤ 54.5981500444688475976718004881740525017616 := by
  have h := exp_mul_bounds exp_two_bounds exp_two_bounds (by norm_num) (by norm_num)
  rw [show (4 : ℝ) = 2 + 2 by norm_num]
  constructor
  · linarith [h.1]
  · linarith [h.2]

theorem exp_five_bounds : (148.41315905915872531490773076882640238847614219051643 : ℝ) ≤ Real.exp (5) ∧ Real.exp (5) ≤ 148.41315914105595036353401893364813610956092676926176 := by
  have h := exp_mul_bounds exp_four_bounds exp_one_bounds (by norm_num) (by norm_num)
  rw [show (5 : ℝ) = 4 + 1 by norm_num]
  constructor
  · linarith [h.1]
  · linarith [h.2]

theorem exp_six_bounds : (403.428793351108687708904879640089597729858414644567768261588969 : ℝ) ≤ Real.exp (6) ∧ Real.exp (6) ≤ 403.428793618252374089098087745264077492878965961459547244854336 := by
  have h := exp_mul_bounds exp_three_bounds exp_three_bounds (by norm_num) (by norm_num)
  rw [show (6 : ℝ) = 3 + 3 by norm_num]
  constructor
  · linarith [h.1]
  · linarith [h.2]

/-- Chamber `[3/10, 7/20]`. -/
theorem key_chamber_2 :
    keyLHS (49 / 100000000) 2.0137528 (1 / 1.8221183) ((2.0137528 + 1 / 2.0137528) / 2 - 1)
        (2.0137528 - 1 / 2.0137528) (7/20)
        (1 / (1 + 12 * 1.8221183 * ((1.8221183 + 1 / 1.8221183) / 2 - 1))) <
      keyRHS 1.8221183 (3/10) := by
  unfold keyLHS keyRHS C5LikelihoodAffineData.compensationDiffBoundE C5LikelihoodAffineData.slopeDiffBound
    C5LikelihoodAffineData.centerZeroBound C5LikelihoodAffineData.centerDiffBound
    C5LikelihoodAffineData.boseZeroBoundE C5LikelihoodAffineData.boseDiffBoundE
  norm_num

/-- Chamber `[7/20, 2/5]`. -/
theorem key_chamber_3 :
    keyLHS (49 / 100000000) 2.2255411 (1 / 2.0137511) ((2.2255411 + 1 / 2.2255411) / 2 - 1)
        (2.2255411 - 1 / 2.2255411) (2/5)
        (1 / (1 + 12 * 2.0137511 * ((2.0137511 + 1 / 2.0137511) / 2 - 1))) <
      keyRHS 2.0137511 (7/20) := by
  unfold keyLHS keyRHS C5LikelihoodAffineData.compensationDiffBoundE C5LikelihoodAffineData.slopeDiffBound
    C5LikelihoodAffineData.centerZeroBound C5LikelihoodAffineData.centerDiffBound
    C5LikelihoodAffineData.boseZeroBoundE C5LikelihoodAffineData.boseDiffBoundE
  norm_num

/-- Chamber `[2/5, 1/2]`. -/
theorem key_chamber_4 :
    keyLHS (49 / 100000000) 2.7182818286 (1 / 2.2255363) ((2.7182818286 + 1 / 2.7182818286) / 2 - 1)
        (2.7182818286 - 1 / 2.7182818286) (1/2)
        (1 / (1 + 12 * 2.2255363 * ((2.2255363 + 1 / 2.2255363) / 2 - 1))) <
      keyRHS 2.2255363 (2/5) := by
  unfold keyLHS keyRHS C5LikelihoodAffineData.compensationDiffBoundE C5LikelihoodAffineData.slopeDiffBound
    C5LikelihoodAffineData.centerZeroBound C5LikelihoodAffineData.centerDiffBound
    C5LikelihoodAffineData.boseZeroBoundE C5LikelihoodAffineData.boseDiffBoundE
  norm_num

/-- Chamber `[1/2, 3/5]`. -/
theorem key_chamber_5 :
    keyLHS (49 / 100000000) 3.32011728573721 (1 / 2.7182818283) ((3.32011728573721 + 1 / 3.32011728573721) / 2 - 1)
        (3.32011728573721 - 1 / 3.32011728573721) (3/5)
        (1 / (1 + 12 * 2.7182818283 * ((2.7182818283 + 1 / 2.7182818283) / 2 - 1))) <
      keyRHS 2.7182818283 (1/2) := by
  unfold keyLHS keyRHS C5LikelihoodAffineData.compensationDiffBoundE C5LikelihoodAffineData.slopeDiffBound
    C5LikelihoodAffineData.centerZeroBound C5LikelihoodAffineData.centerDiffBound
    C5LikelihoodAffineData.boseZeroBoundE C5LikelihoodAffineData.boseDiffBoundE
  norm_num

/-- Chamber `[3/5, 3/4]`. -/
theorem key_chamber_6 :
    keyLHS (49 / 100000000) 4.48168915021576918 (1 / 3.32011509919489) ((4.48168915021576918 + 1 / 4.48168915021576918) / 2 - 1)
        (4.48168915021576918 - 1 / 4.48168915021576918) (3/4)
        (1 / (1 + 12 * 3.32011509919489 * ((3.32011509919489 + 1 / 3.32011509919489) / 2 - 1))) <
      keyRHS 3.32011509919489 (3/5) := by
  unfold keyLHS keyRHS C5LikelihoodAffineData.compensationDiffBoundE C5LikelihoodAffineData.slopeDiffBound
    C5LikelihoodAffineData.centerZeroBound C5LikelihoodAffineData.centerDiffBound
    C5LikelihoodAffineData.boseZeroBoundE C5LikelihoodAffineData.boseDiffBoundE
  norm_num

/-- Chamber `[3/4, 1]`. -/
theorem key_chamber_7 :
    keyLHS (49 / 100000000) 7.38905609969695977796 (1 / 4.48168860606478713) ((7.38905609969695977796 + 1 / 7.38905609969695977796) / 2 - 1)
        (7.38905609969695977796 - 1 / 7.38905609969695977796) (1)
        (1 / (1 + 12 * 4.48168860606478713 * ((4.48168860606478713 + 1 / 4.48168860606478713) / 2 - 1))) <
      keyRHS 4.48168860606478713 (3/4) := by
  unfold keyLHS keyRHS C5LikelihoodAffineData.compensationDiffBoundE C5LikelihoodAffineData.slopeDiffBound
    C5LikelihoodAffineData.centerZeroBound C5LikelihoodAffineData.centerDiffBound
    C5LikelihoodAffineData.boseZeroBoundE C5LikelihoodAffineData.boseDiffBoundE
  norm_num

/-- Chamber `[1, 5/4]`. -/
theorem key_chamber_8 :
    keyLHS (49 / 100000000) 12.182494178465301131165922548 (1 / 7.38905609806599068089) ((12.182494178465301131165922548 + 1 / 12.182494178465301131165922548) / 2 - 1)
        (12.182494178465301131165922548 - 1 / 12.182494178465301131165922548) (5/4)
        (1 / (1 + 12 * 7.38905609806599068089 * ((7.38905609806599068089 + 1 / 7.38905609806599068089) / 2 - 1))) <
      keyRHS 7.38905609806599068089 (1) := by
  unfold keyLHS keyRHS C5LikelihoodAffineData.compensationDiffBoundE C5LikelihoodAffineData.slopeDiffBound
    C5LikelihoodAffineData.centerZeroBound C5LikelihoodAffineData.centerDiffBound
    C5LikelihoodAffineData.boseZeroBoundE C5LikelihoodAffineData.boseDiffBoundE
  norm_num

/-- Chamber `[5/4, 3/2]`. -/
theorem key_chamber_9 :
    keyLHS (49 / 100000000) 20.085536926312235731093758777656 (1 / 12.182492697965068027986709779) ((20.085536926312235731093758777656 + 1 / 20.085536926312235731093758777656) / 2 - 1)
        (20.085536926312235731093758777656 - 1 / 20.085536926312235731093758777656) (3/2)
        (1 / (1 + 12 * 12.182492697965068027986709779 * ((12.182492697965068027986709779 + 1 / 12.182492697965068027986709779) / 2 - 1))) <
      keyRHS 12.182492697965068027986709779 (5/4) := by
  unfold keyLHS keyRHS C5LikelihoodAffineData.compensationDiffBoundE C5LikelihoodAffineData.slopeDiffBound
    C5LikelihoodAffineData.centerZeroBound C5LikelihoodAffineData.centerDiffBound
    C5LikelihoodAffineData.boseZeroBoundE C5LikelihoodAffineData.boseDiffBoundE
  norm_num

/-- Chamber `[3/2, 2]`. -/
theorem key_chamber_10 :
    keyLHS (49 / 100000000) 54.5981500444688475976718004881740525017616 (1 / 20.085536919662085242100431071187) ((54.5981500444688475976718004881740525017616 + 1 / 54.5981500444688475976718004881740525017616) / 2 - 1)
        (54.5981500444688475976718004881740525017616 - 1 / 54.5981500444688475976718004881740525017616) (2)
        (1 / (1 + 12 * 20.085536919662085242100431071187 * ((20.085536919662085242100431071187 + 1 / 20.085536919662085242100431071187) / 2 - 1))) <
      keyRHS 20.085536919662085242100431071187 (3/2) := by
  unfold keyLHS keyRHS C5LikelihoodAffineData.compensationDiffBoundE C5LikelihoodAffineData.slopeDiffBound
    C5LikelihoodAffineData.centerZeroBound C5LikelihoodAffineData.centerDiffBound
    C5LikelihoodAffineData.boseZeroBoundE C5LikelihoodAffineData.boseDiffBoundE
  norm_num

/-- Chamber `[2, 5/2]`. -/
theorem key_chamber_11 :
    keyLHS (49 / 100000000) 148.41315914105595036353401893364813610956092676926176 (1 / 54.5981500203662032900872079044043258111921) ((148.41315914105595036353401893364813610956092676926176 + 1 / 148.41315914105595036353401893364813610956092676926176) / 2 - 1)
        (148.41315914105595036353401893364813610956092676926176 - 1 / 148.41315914105595036353401893364813610956092676926176) (5/2)
        (1 / (1 + 12 * 54.5981500203662032900872079044043258111921 * ((54.5981500203662032900872079044043258111921 + 1 / 54.5981500203662032900872079044043258111921) / 2 - 1))) <
      keyRHS 54.5981500203662032900872079044043258111921 (2) := by
  unfold keyLHS keyRHS C5LikelihoodAffineData.compensationDiffBoundE C5LikelihoodAffineData.slopeDiffBound
    C5LikelihoodAffineData.centerZeroBound C5LikelihoodAffineData.centerDiffBound
    C5LikelihoodAffineData.boseZeroBoundE C5LikelihoodAffineData.boseDiffBoundE
  norm_num

/-- Chamber `[5/2, 3]`. -/
theorem key_chamber_12 :
    keyLHS (49 / 100000000) 403.428793618252374089098087745264077492878965961459547244854336 (1 / 148.41315905915872531490773076882640238847614219051643) ((403.428793618252374089098087745264077492878965961459547244854336 + 1 / 403.428793618252374089098087745264077492878965961459547244854336) / 2 - 1)
        (403.428793618252374089098087745264077492878965961459547244854336 - 1 / 403.428793618252374089098087745264077492878965961459547244854336) (3)
        (1 / (1 + 12 * 148.41315905915872531490773076882640238847614219051643 * ((148.41315905915872531490773076882640238847614219051643 + 1 / 148.41315905915872531490773076882640238847614219051643) / 2 - 1))) <
      keyRHS 148.41315905915872531490773076882640238847614219051643 (5/2) := by
  unfold keyLHS keyRHS C5LikelihoodAffineData.compensationDiffBoundE C5LikelihoodAffineData.slopeDiffBound
    C5LikelihoodAffineData.centerZeroBound C5LikelihoodAffineData.centerDiffBound
    C5LikelihoodAffineData.boseZeroBoundE C5LikelihoodAffineData.boseDiffBoundE
  norm_num

/-! ## Large `t`: the exponential shape -/

/-- Right side with the exponential shape `32 sinh 2t cosh² 2t`. -/
noncomputable def keyRHSexp (w t : ℝ) : ℝ :=
  (288 * w ^ (2 : ℕ) - 72) * (32 * Real.sinh (2 * t) * Real.cosh (2 * t) ^ (2 : ℕ))

theorem keyRHSexp_ge {w t : ℝ} (hw : w = Real.exp (2 * t)) (hw403 : 403 ≤ w) :
    552 * w ^ (5 : ℕ) ≤ keyRHSexp w t := by
  unfold keyRHSexp
  have hw0 : 0 < w := by linarith
  have hsinh : Real.sinh (2 * t) = (w - 1 / w) / 2 := by
    rw [Real.sinh_eq, Real.exp_neg, ← hw]; ring
  have hcosh : Real.cosh (2 * t) = (w + 1 / w) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg, ← hw]; ring
  have hinv : 1 / w ≤ 1 := by rw [div_le_one hw0]; linarith
  have hinv0 : 0 ≤ 1 / w := by positivity
  have hs : w / 4 ≤ Real.sinh (2 * t) := by rw [hsinh]; linarith
  have hc : w / 2 ≤ Real.cosh (2 * t) := by rw [hcosh]; linarith
  have hc2 : (w / 2) ^ (2 : ℕ) ≤ Real.cosh (2 * t) ^ (2 : ℕ) := pow_le_pow_left₀ (by positivity) hc 2
  have hsc : (w / 4) * (w / 2) ^ (2 : ℕ) ≤ Real.sinh (2 * t) * Real.cosh (2 * t) ^ (2 : ℕ) :=
    mul_le_mul hs hc2 (by positivity) (by linarith)
  have hsq : 403 ^ (2 : ℕ) ≤ w ^ (2 : ℕ) := pow_le_pow_left₀ (by norm_num) hw403 2
  have hfac : 287 * w ^ (2 : ℕ) ≤ 288 * w ^ (2 : ℕ) - 72 := by linarith
  have e : 287 * w ^ (2 : ℕ) * (32 * ((w / 4) * (w / 2) ^ (2 : ℕ))) = 574 * w ^ (5 : ℕ) := by ring
  have h5 : 0 < w ^ (5 : ℕ) := by positivity
  calc 552 * w ^ (5 : ℕ) ≤ 287 * w ^ (2 : ℕ) * (32 * ((w / 4) * (w / 2) ^ (2 : ℕ))) := by rw [e]; linarith
    _ ≤ (288 * w ^ (2 : ℕ) - 72) * (32 * (Real.sinh (2 * t) * Real.cosh (2 * t) ^ (2 : ℕ))) :=
        mul_le_mul hfac (by linarith) (by positivity) (by linarith)
    _ = _ := by ring

/-- The crude large-`t` left side as an explicit polynomial. -/
theorem keyLHS_largeT_eq (w t : ℝ) (hw0 : w ≠ 0) :
    keyLHS (49 / 100000000) w 1 (w / 2) w t (1 / (3 * w ^ (2 : ℕ))) =
      ((75411 / 3125000 * w ^ (4 : ℕ) + 58653 / 12500000 * w ^ (3 : ℕ) + 3695139 / 78125000000000 * w ^ (2 : ℕ)) +
        (164052 / 390625 * w ^ (6 : ℕ) + 158319 / 781250 * w ^ (5 : ℕ) + 20298914426427 / 19531250000000 * w ^ (4 : ℕ) +
          29648127132519 / 78125000000000 * w ^ (3 : ℕ) + 10935361398702257853 / 488281250000000000000 * w ^ (2 : ℕ) +
          2532314217069 / 15258789062500000000 * w + 85766121 / 61035156250000000000) * t +
        (2093427 / 390625 * w ^ (6 : ℕ) + 6753327 / 1562500 * w ^ (5 : ℕ) + 102237463826547 / 9765625000000 * w ^ (4 : ℕ) +
          26141457617499 / 7812500000000 * w ^ (3 : ℕ) + 176154704575741197621 / 488281250000000000000 * w ^ (2 : ℕ) +
          298721716340060433 / 15258789062500000000 * w + 19452988668897 / 61035156250000000000) * t ^ (2 : ℕ)) /
        w ^ (2 : ℕ) := by
  unfold keyLHS C5LikelihoodAffineData.compensationDiffBoundE C5LikelihoodAffineData.slopeDiffBound
    C5LikelihoodAffineData.centerZeroBound C5LikelihoodAffineData.centerDiffBound
    C5LikelihoodAffineData.boseZeroBoundE C5LikelihoodAffineData.boseDiffBoundE
  field_simp
  ring

theorem keyLHS_largeT_le {w t : ℝ} (hw : 403 ≤ w) (ht1 : 1 ≤ t) (htw : t ^ (2 : ℕ) ≤ w) :
    keyLHS (49 / 100000000) w 1 (w / 2) w t (1 / (3 * w ^ (2 : ℕ))) ≤ 6 * w ^ (5 : ℕ) := by
  have hw0 : 0 < w := by linarith
  have hw1 : 1 ≤ w := by linarith
  rw [keyLHS_largeT_eq w t hw0.ne', div_le_iff₀ (by positivity)]
  have ht2 : t ≤ w := by nlinarith
  have hβ : 0 ≤ 164052 / 390625 * w ^ (6 : ℕ) + 158319 / 781250 * w ^ (5 : ℕ) + 20298914426427 / 19531250000000 * w ^ (4 : ℕ) +
      29648127132519 / 78125000000000 * w ^ (3 : ℕ) + 10935361398702257853 / 488281250000000000000 * w ^ (2 : ℕ) +
      2532314217069 / 15258789062500000000 * w + 85766121 / 61035156250000000000 := by positivity
  have hγ : 0 ≤ 2093427 / 390625 * w ^ (6 : ℕ) + 6753327 / 1562500 * w ^ (5 : ℕ) + 102237463826547 / 9765625000000 * w ^ (4 : ℕ) +
      26141457617499 / 7812500000000 * w ^ (3 : ℕ) + 176154704575741197621 / 488281250000000000000 * w ^ (2 : ℕ) +
      298721716340060433 / 15258789062500000000 * w + 19452988668897 / 61035156250000000000 := by positivity
  have h1 := mul_le_mul_of_nonneg_left ht2 hβ
  have h2 := mul_le_mul_of_nonneg_left htw hγ
  have p1 : w ≤ w ^ (6 : ℕ) := by simpa using pow_le_pow_right₀ hw1 (show 1 ≤ 6 by norm_num)
  have p2 : w ^ (2 : ℕ) ≤ w ^ (6 : ℕ) := pow_le_pow_right₀ hw1 (by norm_num)
  have p3 : w ^ (3 : ℕ) ≤ w ^ (6 : ℕ) := pow_le_pow_right₀ hw1 (by norm_num)
  have p4 : w ^ (4 : ℕ) ≤ w ^ (6 : ℕ) := pow_le_pow_right₀ hw1 (by norm_num)
  have p5 : w ^ (5 : ℕ) ≤ w ^ (6 : ℕ) := pow_le_pow_right₀ hw1 (by norm_num)
  have p0 : (1 : ℝ) ≤ w ^ (6 : ℕ) := one_le_pow₀ hw1
  have p7 : 403 * w ^ (6 : ℕ) ≤ w ^ (7 : ℕ) := by
    have : w ^ (7 : ℕ) = w ^ (6 : ℕ) * w := by ring
    rw [this]; nlinarith [pow_pos hw0 6]
  have e5 : 6 * w ^ (5 : ℕ) * w ^ (2 : ℕ) = 6 * w ^ (7 : ℕ) := by ring
  rw [e5]
  nlinarith

/-- The key for `t ≥ 3` against the exponential shape. -/
theorem key_largeT {ε w z zp t eq : ℝ} (ht : 3 ≤ t) (hw : w = Real.exp (2 * t))
    (hε0 : 0 ≤ ε) (hε : ε ≤ 49 / 100000000)
    (hz : z = (w + 1 / w) / 2 - 1) (hzp : zp = w - 1 / w) (heq0 : 0 ≤ eq)
    (heq : eq ≤ 1 / (1 + 12 * w * z)) :
    keyLHS ε w (1 / w) z zp t eq < keyRHSexp w t := by
  have hw403 : 403 ≤ w := by
    rw [hw]
    have h1 := exp_six_bounds.1
    have h2 := Real.exp_le_exp.mpr (show (6 : ℝ) ≤ 2 * t by linarith)
    linarith
  have hw0 : 0 < w := by linarith
  have hinv1 : 1 / w ≤ 1 := by rw [div_le_one hw0]; linarith
  have hinv0 : 0 ≤ 1 / w := by positivity
  have hcosh : Real.cosh (2 * t) = (w + 1 / w) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg, ← hw]; ring
  have htw : t ^ (2 : ℕ) ≤ w := by
    have h1 := one_add_sq_div_two_le_cosh' (2 * t)
    rw [hcosh] at h1
    nlinarith
  have hz0 : 0 ≤ z := by rw [hz]; nlinarith
  have hzw : z ≤ w / 2 := by rw [hz]; linarith
  have hzp0 : 0 ≤ zp := by rw [hzp]; linarith
  have hzpw : zp ≤ w := by rw [hzp]; linarith
  have hzlow : w / 2 - 1 ≤ z := by rw [hz]; linarith
  have heq' : eq ≤ 1 / (3 * w ^ (2 : ℕ)) := by
    refine le_trans heq (one_div_le_one_div_of_le (by positivity) ?_)
    have : 12 * w * (w / 2 - 1) ≤ 12 * w * z := mul_le_mul_of_nonneg_left hzlow (by positivity)
    nlinarith
  have h5 : 0 < w ^ (5 : ℕ) := by positivity
  calc keyLHS ε w (1 / w) z zp t eq
      ≤ keyLHS (49 / 100000000) w 1 (w / 2) w t (1 / (3 * w ^ (2 : ℕ))) :=
        keyLHS_mono hε0 hw0.le hinv0 hz0 hzp0 (by linarith) heq0 hε le_rfl hinv1 hzw hzpw le_rfl heq'
    _ ≤ 6 * w ^ (5 : ℕ) := keyLHS_largeT_le hw403 (by linarith) htw
    _ < 552 * w ^ (5 : ℕ) := by linarith
    _ ≤ keyRHSexp w t := keyRHSexp_ge hw hw403

/-! ## Absorbing the scale `A(u−t) = 6ρ` -/

/-- The base point with `A(x₀) = 6`. -/
noncomputable def regimeOneBasePoint : ℝ := Real.log (6 / Real.pi) / 2

theorem thetaCuspSingleAtomReflectionScale_basePoint :
    thetaCuspSingleAtomReflectionScale 1 regimeOneBasePoint = 6 := by
  unfold thetaCuspSingleAtomReflectionScale regimeOneBasePoint
  rw [show 2 * (Real.log (6 / Real.pi) / 2) = Real.log (6 / Real.pi) by ring,
    Real.exp_log (by positivity)]
  simp only [Nat.cast_one, one_pow, mul_one]
  field_simp

theorem regimeOneBasePoint_le {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    regimeOneBasePoint ≤ x := by
  have h6 := thetaCuspSingleAtomReflectionScale_basePoint
  unfold thetaCuspSingleAtomReflectionScale at hA h6
  simp only [Nat.cast_one, one_pow, mul_one] at hA h6
  have : Real.exp (2 * regimeOneBasePoint) ≤ Real.exp (2 * x) :=
    le_of_mul_le_mul_left (by linarith) Real.pi_pos
  have := Real.exp_le_exp.mp this
  linarith

/-- `A(x)^k ε(x) ≤ 6^k · 49·10⁻⁸` for `A(x) ≥ 6`, `k ≤ 18`. -/
theorem regimeOne_scale_pow_le {x : ℝ} {k : ℕ} (hk : (k : ℝ) ≤ 18)
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspSingleAtomReflectionScale 1 x ^ k * regimeOneLikelihoodScale x ≤
      6 ^ k * (49 / 100000000) := by
  have h := regimeOne_pow_scale_le_left hk (x := regimeOneBasePoint) (y := x)
    (by rw [thetaCuspSingleAtomReflectionScale_basePoint]) (regimeOneBasePoint_le hA)
  rw [thetaCuspSingleAtomReflectionScale_basePoint] at h
  have hε : regimeOneLikelihoodScale regimeOneBasePoint ≤ 49 / 100000000 := by
    unfold regimeOneLikelihoodScale
    rw [thetaCuspSingleAtomReflectionScale_basePoint]
    have := base_scale_six_lt
    rw [div_mul_eq_mul_div, ← Real.exp_add,
      show 3 * Real.pi + -(3 * (6 : ℝ)) = -(3 * (6 - Real.pi)) by ring] at this
    exact this.le
  calc _ ≤ 6 ^ k * regimeOneLikelihoodScale regimeOneBasePoint := h
    _ ≤ 6 ^ k * (49 / 100000000) := mul_le_mul_of_nonneg_left hε (by positivity)

/-- The correction inputs scale like `ρ⁻⁹` when `A(u−t) = 6ρ`. -/
theorem regimeOne_dInputs_le {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    let Am := thetaCuspSingleAtomReflectionScale 1 x
    let ε := regimeOneLikelihoodScale x
    let ρ := Am / 6
    12 * Am * ε ≤ 72 * (49 / 100000000) / ρ ^ (9 : ℕ) ∧
    76 * Am ^ (2 : ℕ) * ε ≤ 2736 * (49 / 100000000) / ρ ^ (9 : ℕ) ∧
    522 * Am ^ (3 : ℕ) * ε ≤ 112752 * (49 / 100000000) / ρ ^ (9 : ℕ) ∧
    24 * Am * ε ≤ 144 * (49 / 100000000) / ρ ^ (9 : ℕ) ∧
    4 * ε ≤ 4 * (49 / 100000000) / ρ ^ (9 : ℕ) := by
  intro Am ε ρ
  have hε0 : 0 < ε := regimeOneLikelihoodScale_pos x
  have hρ : 1 ≤ ρ := by show 1 ≤ Am / 6; rw [le_div_iff₀ (by norm_num)]; linarith
  have hρ0 : 0 < ρ := by linarith
  have hAm : Am = 6 * ρ := by show Am = 6 * (Am / 6); ring
  have h9 := regimeOne_scale_pow_le (k := 9) (by norm_num) hA
  have h10 := regimeOne_scale_pow_le (k := 10) (by norm_num) hA
  have h11 := regimeOne_scale_pow_le (k := 11) (by norm_num) hA
  have h12 := regimeOne_scale_pow_le (k := 12) (by norm_num) hA
  change Am ^ (9 : ℕ) * ε ≤ _ at h9
  change Am ^ (10 : ℕ) * ε ≤ _ at h10
  change Am ^ (11 : ℕ) * ε ≤ _ at h11
  change Am ^ (12 : ℕ) * ε ≤ _ at h12
  rw [hAm] at h9 h10 h11 h12 ⊢
  have r9 : ρ ^ (9 : ℕ) * ε ≤ 49 / 100000000 := by
    rw [mul_pow] at h9; nlinarith
  have r10 : ρ ^ (10 : ℕ) * ε ≤ 49 / 100000000 := by
    rw [mul_pow] at h10; nlinarith
  have r11 : ρ ^ (11 : ℕ) * ε ≤ 49 / 100000000 := by
    rw [mul_pow] at h11; nlinarith
  have r12 : ρ ^ (12 : ℕ) * ε ≤ 49 / 100000000 := by
    rw [mul_pow] at h12; nlinarith
  have hρ9 : 0 < ρ ^ (9 : ℕ) := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hρ9]
    have : 12 * (6 * ρ) * ε * ρ ^ (9 : ℕ) = 72 * (ρ ^ (10 : ℕ) * ε) := by ring
    rw [this]; linarith
  · rw [le_div_iff₀ hρ9]
    have : 76 * (6 * ρ) ^ (2 : ℕ) * ε * ρ ^ (9 : ℕ) = 2736 * (ρ ^ (11 : ℕ) * ε) := by ring
    rw [this]; linarith
  · rw [le_div_iff₀ hρ9]
    have : 522 * (6 * ρ) ^ (3 : ℕ) * ε * ρ ^ (9 : ℕ) = 112752 * (ρ ^ (12 : ℕ) * ε) := by ring
    rw [this]; linarith
  · rw [le_div_iff₀ hρ9]
    have : 24 * (6 * ρ) * ε * ρ ^ (9 : ℕ) = 144 * (ρ ^ (10 : ℕ) * ε) := by ring
    rw [this]; linarith
  · rw [le_div_iff₀ hρ9]
    have : 4 * ε * ρ ^ (9 : ℕ) = 4 * (ρ ^ (9 : ℕ) * ε) := by ring
    rw [this]; linarith

/-- The single-atom inputs are bounded by `ρ³` times their `ρ = 1` values. -/
theorem regimeOne_hat_inputs_le {A ρ w z z' : ℝ} (hρ : 1 ≤ ρ) (hw : 1 ≤ w) (hz : 0 ≤ z)
    (hz' : 0 ≤ z') (hAeq : A = 6 * ρ * w) :
    (2 * A + 12 / A) * z' ≤ ρ ^ (3 : ℕ) * ((12 * w + 2 * (1 / w)) * z') ∧
    4 * (12 / A) ^ (2 : ℕ) * z * (z + 2) + 4 * (2 * A + 12 / A) * (z + 1) ≤
      ρ ^ (3 : ℕ) * (4 * (2 * (1 / w)) ^ (2 : ℕ) * z * (z + 2) + 4 * (12 * w + 2 * (1 / w)) * (z + 1)) ∧
    z' * (8 * (12 / A) ^ (3 : ℕ) * z * (z + 2) + 12 * (12 / A) ^ (2 : ℕ) * (z + 1) + 4 * (2 * A + 12 / A)) ≤
      ρ ^ (3 : ℕ) * (z' * (8 * (2 * (1 / w)) ^ (3 : ℕ) * z * (z + 2) + 12 * (2 * (1 / w)) ^ (2 : ℕ) * (z + 1) +
        4 * (12 * w + 2 * (1 / w)))) ∧
    4 * A * z + 36 / A * z ≤ ρ ^ (3 : ℕ) * (24 * w * z + 6 * z * (1 / w)) ∧
    (4 * A + 72 / A) * z' ≤ ρ ^ (3 : ℕ) * ((24 * w + 12 * (1 / w)) * z') ∧
    4 * (1728 / A ^ (2 : ℕ) * z * (z + 2) + (4 * A + 72 / A) * (z + 1)) ≤
      ρ ^ (3 : ℕ) * (4 * (48 * (1 / w) ^ (2 : ℕ) * z * (z + 2) + (24 * w + 12 * (1 / w)) * (z + 1))) := by
  have hρ0 : 0 < ρ := by linarith
  have hw0 : 0 < w := by linarith
  have hA0 : 0 < A := by rw [hAeq]; positivity
  have hρ3 : 1 ≤ ρ ^ (3 : ℕ) := one_le_pow₀ hρ
  have hρρ : ρ ≤ ρ ^ (3 : ℕ) := by
    have := mul_le_mul_of_nonneg_left (one_le_pow₀ hρ : (1:ℝ) ≤ ρ ^ (2 : ℕ)) hρ0.le
    linarith
  have hX : 2 * A ≤ ρ ^ (3 : ℕ) * (12 * w) := by
    rw [hAeq]
    have := mul_le_mul_of_nonneg_right hρρ (by positivity : (0:ℝ) ≤ 12 * w)
    linarith
  have hY0 : 0 ≤ 2 * (1 / w) := by positivity
  have hY : 12 / A ≤ 2 * (1 / w) := by
    rw [hAeq, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hYn : 0 ≤ 12 / A := by positivity
  have hYY : 12 / A ≤ ρ ^ (3 : ℕ) * (2 * (1 / w)) := hY.trans (le_mul_of_one_le_left hY0 hρ3)
  have hY2 : (12 / A) ^ (2 : ℕ) ≤ ρ ^ (3 : ℕ) * (2 * (1 / w)) ^ (2 : ℕ) :=
    (pow_le_pow_left₀ hYn hY 2).trans (le_mul_of_one_le_left (by positivity) hρ3)
  have hY3 : (12 / A) ^ (3 : ℕ) ≤ ρ ^ (3 : ℕ) * (2 * (1 / w)) ^ (3 : ℕ) :=
    (pow_le_pow_left₀ hYn hY 3).trans (le_mul_of_one_le_left (by positivity) hρ3)
  have hz1 : 0 ≤ z + 1 := by linarith
  have hzz : 0 ≤ z * (z + 2) := by positivity
  have hz'zz : 0 ≤ z' * (z * (z + 2)) := by positivity
  have hz'z1 : 0 ≤ z' * (z + 1) := by positivity
  have P1 := mul_le_mul_of_nonneg_right hX hz'
  have P2 := mul_le_mul_of_nonneg_right hYY hz'
  have P3 := mul_le_mul_of_nonneg_right hX hz1
  have P4 := mul_le_mul_of_nonneg_right hYY hz1
  have P5 := mul_le_mul_of_nonneg_right hX hz
  have P6 := mul_le_mul_of_nonneg_right hYY hz
  have P7 := mul_le_mul_of_nonneg_right hY2 hzz
  have P8 := mul_le_mul_of_nonneg_right hY3 hz'zz
  have P9 := mul_le_mul_of_nonneg_right hY2 hz'z1
  have e1728 : 1728 / A ^ (2 : ℕ) = 12 * (12 / A) ^ (2 : ℕ) := by field_simp; ring
  have e36 : 36 / A = 3 * (12 / A) := by ring
  have e72 : 72 / A = 6 * (12 / A) := by ring
  have e48 : 48 * (1 / w) ^ (2 : ℕ) = 12 * (2 * (1 / w)) ^ (2 : ℕ) := by ring
  have e6 : 6 * z * (1 / w) = 3 * z * (2 * (1 / w)) := by ring
  have e12 : 12 * (1 / w) = 6 * (2 * (1 / w)) := by ring
  rw [e1728, e36, e72, e48, e6, e12]
  generalize 12 / A = Y at *
  generalize 2 * (1 / w) = Y0 at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith [P1, P2, P3, P4, P5, P6, P7, P8, P9]

/-- `e^{-q} ≤ 1/(1 + 12 w z)` for the single-atom action at `A(u) ≥ 6w`. -/
theorem exp_neg_action_le {u t w : ℝ} (ht : 0 ≤ t) (htu : t ≤ u)
    (hA : 6 * w ≤ thetaCuspSingleAtomReflectionScale 1 u) (hw : 0 ≤ w) :
    Real.exp (-thetaCuspSingleAtomReflectedAction (thetaCuspSingleAtomReflectionScale 1 u) t) ≤
      1 / (1 + 12 * w * thetaCuspSingleAtomReflectionDefect t) := by
  have hr0 := one_half_lt_thetaCuspSingleAtomReflectionFactor_of_sameHalfLine ht htu
  have hA3 := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) (le_trans ht htu)
  set A := thetaCuspSingleAtomReflectionScale 1 u with hAdef
  set z := thetaCuspSingleAtomReflectionDefect t with hzdef
  have hz0 : 0 ≤ z := by
    show 0 ≤ Real.cosh (2 * t) - 1
    linarith [Real.one_le_cosh (2 * t)]
  have hq : 12 * w * z ≤ thetaCuspSingleAtomReflectedAction A t := by
    unfold thetaCuspSingleAtomReflectedAction
    rw [← hzdef]
    have hr1 : thetaCuspSingleAtomReflectionFactor A z ≤ 1 := by
      unfold thetaCuspSingleAtomReflectionFactor
      have := mul_nonneg (thetaCuspSingleAtomReflectionLambda_pos hA3).le hz0
      linarith
    have hlog : Real.log (thetaCuspSingleAtomReflectionFactor A z) ≤ 0 :=
      Real.log_nonpos (by linarith) hr1
    have := mul_le_mul_of_nonneg_right hA hz0
    linarith
  have h1 : 1 + 12 * w * z ≤ Real.exp (12 * w * z) := by
    have := Real.add_one_le_exp (12 * w * z); linarith
  have h2 : Real.exp (12 * w * z) ≤ Real.exp (thetaCuspSingleAtomReflectedAction A t) :=
    Real.exp_le_exp.mpr hq
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by positivity) (h1.trans h2)

/-- The scaled key: from the `ρ = 1` key at `(w, t)` to the actual inputs. -/
theorem key_scaled {u t : ℝ} (ht : 1 / 4 ≤ t) (htu : t ≤ u)
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t)) :
    let A := thetaCuspSingleAtomReflectionScale 1 u
    let Am := thetaCuspSingleAtomReflectionScale 1 (u - t)
    let ε := regimeOneLikelihoodScale (u - t)
    let z := thetaCuspSingleAtomReflectionDefect t
    let z' := 2 * Real.sinh (2 * t)
    let w := Real.exp (2 * t)
    C5LikelihoodAffineData.compensationDiffBound t
        ((2 * A + 12 / A) * z')
        (4 * (12 / A) ^ (2 : ℕ) * z * (z + 2) + 4 * (2 * A + 12 / A) * (z + 1))
        (z' * (8 * (12 / A) ^ (3 : ℕ) * z * (z + 2) + 12 * (12 / A) ^ (2 : ℕ) * (z + 1) + 4 * (2 * A + 12 / A)))
        (4 * A * z + 36 / A * z) ((4 * A + 72 / A) * z')
        (4 * (1728 / A ^ (2 : ℕ) * z * (z + 2) + (4 * A + 72 / A) * (z + 1)))
        (12 * Am * ε) (76 * Am ^ (2 : ℕ) * ε) (522 * Am ^ (3 : ℕ) * ε) (24 * Am * ε) (76 * Am ^ (2 : ℕ) * ε)
        (522 * Am ^ (3 : ℕ) * ε) (4 * ε) (thetaCuspSingleAtomReflectedAction A t) ≤
      keyLHS (49 / 100000000) w (1 / w) z z' t (1 / (1 + 12 * w * z)) := by
  intro A Am ε z z' w
  have ht0 : 0 < t := by linarith
  have hw1 : 1 ≤ w := by
    show 1 ≤ Real.exp (2 * t); rw [Real.one_le_exp_iff]; linarith
  have hw0 : 0 < w := by linarith
  have hz0 : 0 ≤ z := by
    show 0 ≤ Real.cosh (2 * t) - 1
    linarith [Real.one_le_cosh (2 * t)]
  have hz'0 : 0 ≤ z' := by
    show 0 ≤ 2 * Real.sinh (2 * t)
    have := Real.sinh_nonneg_iff.mpr (by linarith : (0:ℝ) ≤ 2 * t)
    linarith
  have hAm6 : 6 ≤ Am := hA
  have hAeq : A = Am * w := by
    show thetaCuspSingleAtomReflectionScale 1 u = thetaCuspSingleAtomReflectionScale 1 (u - t) * Real.exp (2 * t)
    unfold thetaCuspSingleAtomReflectionScale
    rw [show (2 : ℝ) * u = 2 * (u - t) + 2 * t by ring, Real.exp_add]
    ring
  set ρ := Am / 6 with hρdef
  have hρ : 1 ≤ ρ := by rw [hρdef, le_div_iff₀ (by norm_num)]; linarith
  have hAρ : A = 6 * ρ * w := by rw [hAeq, hρdef]; ring
  have hA0 : 0 < A := by rw [hAρ]; positivity
  have hAw : 6 * w ≤ A := by
    rw [hAρ]
    have := mul_le_mul_of_nonneg_right hρ (by positivity : (0:ℝ) ≤ 6 * w)
    linarith
  obtain ⟨ha, hb, hc, hs, hm, hn⟩ := regimeOne_hat_inputs_le hρ hw1 hz0 hz'0 hAρ
  obtain ⟨hda, hdb, hdc, hds, hdq⟩ := regimeOne_dInputs_le hA
  have heq : Real.exp (-thetaCuspSingleAtomReflectedAction A t) ≤ 1 / (1 + 12 * w * z) :=
    exp_neg_action_le ht0.le htu hAw hw0.le
  have hε0 : 0 < ε := regimeOneLikelihoodScale_pos (u - t)
  have hAm0 : 0 < Am := by linarith
  have heq0 : 0 ≤ Real.exp (-thetaCuspSingleAtomReflectedAction A t) := (Real.exp_pos _).le
  rw [C5LikelihoodAffineData.compensationDiffBound_eq_E]
  have hz1 : 0 ≤ z + 1 := by linarith
  have hzz : 0 ≤ z + 2 := by linarith
  have hinv0 : 0 ≤ 1 / w := by positivity
  have step1 := C5LikelihoodAffineData.compensationDiffBoundE_mono (t := t)
    (a' := (2 * A + 12 / A) * z')
    (b' := 4 * (12 / A) ^ (2 : ℕ) * z * (z + 2) + 4 * (2 * A + 12 / A) * (z + 1))
    (c' := z' * (8 * (12 / A) ^ (3 : ℕ) * z * (z + 2) + 12 * (12 / A) ^ (2 : ℕ) * (z + 1) + 4 * (2 * A + 12 / A)))
    (s' := 4 * A * z + 36 / A * z) (m' := (4 * A + 72 / A) * z')
    (n' := 4 * (1728 / A ^ (2 : ℕ) * z * (z + 2) + (4 * A + 72 / A) * (z + 1)))
    (da' := 12 * Am * ε) (db' := 76 * Am ^ (2 : ℕ) * ε) (dc' := 522 * Am ^ (3 : ℕ) * ε) (ds' := 24 * Am * ε)
    (dm' := 76 * Am ^ (2 : ℕ) * ε) (dn' := 522 * Am ^ (3 : ℕ) * ε) (dq' := 4 * ε)
    (eq := Real.exp (-thetaCuspSingleAtomReflectedAction A t))
    (a'' := ρ ^ (3 : ℕ) * ((12 * w + 2 * (1 / w)) * z'))
    (b'' := ρ ^ (3 : ℕ) * (4 * (2 * (1 / w)) ^ (2 : ℕ) * z * (z + 2) + 4 * (12 * w + 2 * (1 / w)) * (z + 1)))
    (c'' := ρ ^ (3 : ℕ) * (z' * (8 * (2 * (1 / w)) ^ (3 : ℕ) * z * (z + 2) + 12 * (2 * (1 / w)) ^ (2 : ℕ) * (z + 1) +
        4 * (12 * w + 2 * (1 / w)))))
    (s'' := ρ ^ (3 : ℕ) * (24 * w * z + 6 * z * (1 / w))) (m'' := ρ ^ (3 : ℕ) * ((24 * w + 12 * (1 / w)) * z'))
    (n'' := ρ ^ (3 : ℕ) * (4 * (48 * (1 / w) ^ (2 : ℕ) * z * (z + 2) + (24 * w + 12 * (1 / w)) * (z + 1))))
    (da'' := 72 * (49 / 100000000) / ρ ^ (9 : ℕ)) (db'' := 2736 * (49 / 100000000) / ρ ^ (9 : ℕ))
    (dc'' := 112752 * (49 / 100000000) / ρ ^ (9 : ℕ)) (ds'' := 144 * (49 / 100000000) / ρ ^ (9 : ℕ))
    (dm'' := 2736 * (49 / 100000000) / ρ ^ (9 : ℕ)) (dn'' := 112752 * (49 / 100000000) / ρ ^ (9 : ℕ))
    (dq'' := 4 * (49 / 100000000) / ρ ^ (9 : ℕ)) (eq' := 1 / (1 + 12 * w * z))
    ht0.le (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) heq0
    ha hb hc hs hm hn hda hdb hdc hds hdb hdc hdq heq
  have step2 := C5LikelihoodAffineData.compensationDiffBoundE_scale (ρ := ρ) (t := t)
    (a' := (12 * w + 2 * (1 / w)) * z')
    (b' := 4 * (2 * (1 / w)) ^ (2 : ℕ) * z * (z + 2) + 4 * (12 * w + 2 * (1 / w)) * (z + 1))
    (c' := z' * (8 * (2 * (1 / w)) ^ (3 : ℕ) * z * (z + 2) + 12 * (2 * (1 / w)) ^ (2 : ℕ) * (z + 1) +
        4 * (12 * w + 2 * (1 / w))))
    (s' := 24 * w * z + 6 * z * (1 / w)) (m' := (24 * w + 12 * (1 / w)) * z')
    (n' := 4 * (48 * (1 / w) ^ (2 : ℕ) * z * (z + 2) + (24 * w + 12 * (1 / w)) * (z + 1)))
    (da' := 72 * (49 / 100000000)) (db' := 2736 * (49 / 100000000)) (dc' := 112752 * (49 / 100000000))
    (ds' := 144 * (49 / 100000000)) (dm' := 2736 * (49 / 100000000)) (dn' := 112752 * (49 / 100000000))
    (dq' := 4 * (49 / 100000000)) (eq := 1 / (1 + 12 * w * z))
    hρ ht0.le (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity)
  exact step1.trans step2

/-- Chamber selection: the `ρ = 1` key on `[ta, tb]` from the corner instance. -/
theorem key_in_chamber {t ta tb wa wb : ℝ} (hta : ta ≤ t) (htb : t ≤ tb) (hta0 : 0 ≤ ta)
    (hwa1 : 1 ≤ wa) (hwa : wa ≤ Real.exp (2 * ta)) (hwb : Real.exp (2 * tb) ≤ wb)
    (hnum : keyLHS (49 / 100000000) wb (1 / wa) ((wb + 1 / wb) / 2 - 1) (wb - 1 / wb) tb
        (1 / (1 + 12 * wa * ((wa + 1 / wa) / 2 - 1))) < keyRHS wa ta) :
    keyLHS (49 / 100000000) (Real.exp (2 * t)) (1 / Real.exp (2 * t))
        (thetaCuspSingleAtomReflectionDefect t) (2 * Real.sinh (2 * t)) t
        (1 / (1 + 12 * Real.exp (2 * t) * thetaCuspSingleAtomReflectionDefect t)) <
      keyRHS (Real.exp (2 * t)) t := by
  set w := Real.exp (2 * t) with hwdef
  have hw1 : 1 ≤ w := by rw [hwdef, Real.one_le_exp_iff]; linarith
  have hw0 : 0 < w := by linarith
  have hwa0 : 0 < wa := by linarith
  have hwlo : wa ≤ w := hwa.trans (Real.exp_le_exp.mpr (by linarith))
  have hwhi : w ≤ wb := (Real.exp_le_exp.mpr (by linarith)).trans hwb
  have hz : thetaCuspSingleAtomReflectionDefect t = (w + 1 / w) / 2 - 1 := by
    show Real.cosh (2 * t) - 1 = _
    rw [Real.cosh_eq, Real.exp_neg, hwdef]; ring
  have hzp : 2 * Real.sinh (2 * t) = w - 1 / w := by
    rw [Real.sinh_eq, Real.exp_neg, hwdef]; ring
  rw [hz, hzp]
  obtain ⟨hzb, hzpb⟩ := defect_le_of_le hw1 hwhi
  obtain ⟨hza, -⟩ := defect_le_of_le hwa1 hwlo
  have hwne : w ≠ 0 := hw0.ne'
  have hwane : wa ≠ 0 := hwa0.ne'
  have hz0 : 0 ≤ (w + 1 / w) / 2 - 1 := by
    have e : (w + 1 / w) / 2 - 1 = (w - 1) ^ (2 : ℕ) / (2 * w) := by field_simp; ring
    rw [e]; positivity
  have hzp0 : 0 ≤ w - 1 / w := by
    rw [sub_nonneg, div_le_iff₀ hw0]; nlinarith
  have hza0 : 0 ≤ (wa + 1 / wa) / 2 - 1 := by
    have e : (wa + 1 / wa) / 2 - 1 = (wa - 1) ^ (2 : ℕ) / (2 * wa) := by field_simp; ring
    rw [e]; positivity
  have heq : 1 / (1 + 12 * w * ((w + 1 / w) / 2 - 1)) ≤
      1 / (1 + 12 * wa * ((wa + 1 / wa) / 2 - 1)) := by
    apply one_div_le_one_div_of_le (by positivity)
    have := mul_le_mul hwlo hza hza0 hw0.le
    linarith
  exact key_of_chamber (by norm_num) hw0.le (by positivity) hz0 hzp0 hta0 (by positivity) hwa1
    le_rfl hwlo hwhi (one_div_le_one_div_of_le hwa0 hwlo) hzb hzpb hta htb heq hnum

/-- **The regime-I key inequality holds** for `1/4 ≤ t ≤ u`, `A(u−t) ≥ 6`. -/
theorem regimeOne_key_holds {u t : ℝ} (ht : 1 / 4 ≤ t) (htu : t ≤ u)
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t)) :
    ∃ sh : ℝ, 0 ≤ sh ∧ sh ≤ c5HyperbolicGaussianBaseShape t ∧
      (let A := thetaCuspSingleAtomReflectionScale 1 u
      let Am := thetaCuspSingleAtomReflectionScale 1 (u - t)
      let ε := regimeOneLikelihoodScale (u - t)
      let z := thetaCuspSingleAtomReflectionDefect t
      let z' := 2 * Real.sinh (2 * t)
      C5LikelihoodAffineData.compensationDiffBound t
        ((2 * A + 12 / A) * z')
        (4 * (12 / A) ^ (2 : ℕ) * z * (z + 2) + 4 * (2 * A + 12 / A) * (z + 1))
        (z' * (8 * (12 / A) ^ (3 : ℕ) * z * (z + 2) + 12 * (12 / A) ^ (2 : ℕ) * (z + 1) + 4 * (2 * A + 12 / A)))
        (4 * A * z + 36 / A * z) ((4 * A + 72 / A) * z')
        (4 * (1728 / A ^ (2 : ℕ) * z * (z + 2) + (4 * A + 72 / A) * (z + 1)))
        (12 * Am * ε) (76 * Am ^ (2 : ℕ) * ε) (522 * Am ^ (3 : ℕ) * ε) (24 * Am * ε) (76 * Am ^ (2 : ℕ) * ε)
        (522 * Am ^ (3 : ℕ) * ε) (4 * ε) (thetaCuspSingleAtomReflectedAction A t) <
      2 * A * (4 * A - 36 / A) * sh) := by
  have hks := key_scaled ht htu hA
  simp only at hks ⊢
  have ht0 : 0 < t := by linarith
  set w := Real.exp (2 * t) with hwdef
  set A := thetaCuspSingleAtomReflectionScale 1 u with hAdef
  set z := thetaCuspSingleAtomReflectionDefect t with hzdef
  have hz0 : 0 ≤ z := by
    rw [hzdef]
    show 0 ≤ Real.cosh (2 * t) - 1
    linarith [Real.one_le_cosh (2 * t)]
  have hw1 : 1 ≤ w := by rw [hwdef, Real.one_le_exp_iff]; linarith
  have hw0 : 0 < w := by linarith
  have hAeq : A = thetaCuspSingleAtomReflectionScale 1 (u - t) * w := by
    rw [hAdef, hwdef]
    unfold thetaCuspSingleAtomReflectionScale
    rw [show (2 : ℝ) * u = 2 * (u - t) + 2 * t by ring, Real.exp_add]
    ring
  have hAw : 6 * w ≤ A := by
    rw [hAeq]; exact mul_le_mul_of_nonneg_right hA hw0.le
  have hA0 : 0 < A := by linarith
  have hfac : 288 * w ^ (2 : ℕ) - 72 ≤ 2 * A * (4 * A - 36 / A) := by
    have e : 2 * A * (4 * A - 36 / A) = 8 * A ^ (2 : ℕ) - 72 := by field_simp; ring
    rw [e]
    have := pow_le_pow_left₀ (by positivity) hAw 2
    nlinarith
  rcases le_or_gt t 3 with ht3 | ht3
  · -- chambers
    refine ⟨6656 / 9 * t ^ (7 : ℕ) + 615872 / 945 * t ^ (9 : ℕ) + 50560 / 189 * t ^ (11 : ℕ), by positivity,
      c5HyperbolicGaussianBaseShape_ge ht0.le, ?_⟩
    have hcase : keyLHS (49 / 100000000) w (1 / w) z (2 * Real.sinh (2 * t)) t
        (1 / (1 + 12 * w * z)) < keyRHS w t := by
      rw [hwdef, hzdef]
      rcases le_or_gt t (3 / 10) with h1 | h1
      · exact key_in_chamber ht h1 (by norm_num) (by norm_num) (by rw [show (2 : ℝ) * (1/4) = 1/2 by norm_num]; exact exp_half_bounds.1) (by rw [show (2 : ℝ) * (3/10) = 3/5 by norm_num]; exact exp_threeFifths_bounds.2) key_chamber_1
      rcases le_or_gt t (7/20) with h2 | h2
      · exact key_in_chamber h1.le h2 (by norm_num) (by norm_num) (by rw [show (2 : ℝ) * (3/10) = 3/5 by norm_num]; exact exp_threeFifths_bounds.1) (by rw [show (2 : ℝ) * (7/20) = 7/10 by norm_num]; exact exp_sevenTenths_bounds.2) key_chamber_2
      rcases le_or_gt t (2/5) with h3 | h3
      · exact key_in_chamber h2.le h3 (by norm_num) (by norm_num) (by rw [show (2 : ℝ) * (7/20) = 7/10 by norm_num]; exact exp_sevenTenths_bounds.1) (by rw [show (2 : ℝ) * (2/5) = 4/5 by norm_num]; exact exp_fourFifths_bounds.2) key_chamber_3
      rcases le_or_gt t (1/2) with h4 | h4
      · exact key_in_chamber h3.le h4 (by norm_num) (by norm_num) (by rw [show (2 : ℝ) * (2/5) = 4/5 by norm_num]; exact exp_fourFifths_bounds.1) (by rw [show (2 : ℝ) * (1/2) = 1 by norm_num]; exact exp_one_bounds.2) key_chamber_4
      rcases le_or_gt t (3/5) with h5 | h5
      · exact key_in_chamber h4.le h5 (by norm_num) (by norm_num) (by rw [show (2 : ℝ) * (1/2) = 1 by norm_num]; exact exp_one_bounds.1) (by rw [show (2 : ℝ) * (3/5) = 6/5 by norm_num]; exact exp_sixFifths_bounds.2) key_chamber_5
      rcases le_or_gt t (3/4) with h6 | h6
      · exact key_in_chamber h5.le h6 (by norm_num) (by norm_num) (by rw [show (2 : ℝ) * (3/5) = 6/5 by norm_num]; exact exp_sixFifths_bounds.1) (by rw [show (2 : ℝ) * (3/4) = 3/2 by norm_num]; exact exp_threeHalves_bounds.2) key_chamber_6
      rcases le_or_gt t (1) with h7 | h7
      · exact key_in_chamber h6.le h7 (by norm_num) (by norm_num) (by rw [show (2 : ℝ) * (3/4) = 3/2 by norm_num]; exact exp_threeHalves_bounds.1) (by rw [show (2 : ℝ) * (1) = 2 by norm_num]; exact exp_two_bounds.2) key_chamber_7
      rcases le_or_gt t (5/4) with h8 | h8
      · exact key_in_chamber h7.le h8 (by norm_num) (by norm_num) (by rw [show (2 : ℝ) * (1) = 2 by norm_num]; exact exp_two_bounds.1) (by rw [show (2 : ℝ) * (5/4) = 5/2 by norm_num]; exact exp_fiveHalves_bounds.2) key_chamber_8
      rcases le_or_gt t (3/2) with h9 | h9
      · exact key_in_chamber h8.le h9 (by norm_num) (by norm_num) (by rw [show (2 : ℝ) * (5/4) = 5/2 by norm_num]; exact exp_fiveHalves_bounds.1) (by rw [show (2 : ℝ) * (3/2) = 3 by norm_num]; exact exp_three_bounds.2) key_chamber_9
      rcases le_or_gt t (2) with h10 | h10
      · exact key_in_chamber h9.le h10 (by norm_num) (by norm_num) (by rw [show (2 : ℝ) * (3/2) = 3 by norm_num]; exact exp_three_bounds.1) (by rw [show (2 : ℝ) * (2) = 4 by norm_num]; exact exp_four_bounds.2) key_chamber_10
      rcases le_or_gt t (5/2) with h11 | h11
      · exact key_in_chamber h10.le h11 (by norm_num) (by norm_num) (by rw [show (2 : ℝ) * (2) = 4 by norm_num]; exact exp_four_bounds.1) (by rw [show (2 : ℝ) * (5/2) = 5 by norm_num]; exact exp_five_bounds.2) key_chamber_11
      exact key_in_chamber h11.le ht3 (by norm_num) (by norm_num) (by rw [show (2 : ℝ) * (5/2) = 5 by norm_num]; exact exp_five_bounds.1) (by rw [show (2 : ℝ) * (3) = 6 by norm_num]; exact exp_six_bounds.2) key_chamber_12
    have hpoly : 0 ≤ 6656 / 9 * t ^ (7 : ℕ) + 615872 / 945 * t ^ (9 : ℕ) + 50560 / 189 * t ^ (11 : ℕ) := by positivity
    have hR : keyRHS w t ≤ 2 * A * (4 * A - 36 / A) *
        (6656 / 9 * t ^ (7 : ℕ) + 615872 / 945 * t ^ (9 : ℕ) + 50560 / 189 * t ^ (11 : ℕ)) := by
      unfold keyRHS
      exact mul_le_mul_of_nonneg_right hfac hpoly
    exact lt_of_le_of_lt hks (lt_of_lt_of_le hcase hR)
  · -- large `t`
    refine ⟨32 * Real.sinh (2 * t) * Real.cosh (2 * t) ^ (2 : ℕ), ?_,
      c5HyperbolicGaussianBaseShape_ge_exp (by linarith), ?_⟩
    · have := Real.sinh_nonneg_iff.mpr (by linarith : (0:ℝ) ≤ 2 * t)
      positivity
    have hz : z = (w + 1 / w) / 2 - 1 := by
      rw [hzdef, hwdef]
      show Real.cosh (2 * t) - 1 = _
      rw [Real.cosh_eq, Real.exp_neg]; ring
    have hzp : 2 * Real.sinh (2 * t) = w - 1 / w := by
      rw [hwdef, Real.sinh_eq, Real.exp_neg]; ring
    have hcase : keyLHS (49 / 100000000) w (1 / w) z (2 * Real.sinh (2 * t)) t
        (1 / (1 + 12 * w * z)) < keyRHSexp w t :=
      key_largeT ht3.le hwdef (by norm_num) le_rfl hz hzp (by positivity) le_rfl
    have hsh0 : 0 ≤ 32 * Real.sinh (2 * t) * Real.cosh (2 * t) ^ (2 : ℕ) := by
      have := Real.sinh_nonneg_iff.mpr (by linarith : (0:ℝ) ≤ 2 * t)
      positivity
    have hR : keyRHSexp w t ≤ 2 * A * (4 * A - 36 / A) *
        (32 * Real.sinh (2 * t) * Real.cosh (2 * t) ^ (2 : ℕ)) := by
      unfold keyRHSexp
      exact mul_le_mul_of_nonneg_right hfac hsh0
    exact lt_of_le_of_lt hks (lt_of_lt_of_le hcase hR)

/-- **Unconditional regime-I gate** for `t ≥ 1/4`: the completed C5 compensation margin is
positive whenever `1/4 ≤ t ≤ u` and `π e^{2(u−t)} ≥ 6`. -/
theorem c5CompletedCompensationMargin_pos_of_regimeOne_quarter {u t : ℝ} (ht : 1 / 4 ≤ t)
    (htu : t ≤ u) (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t)) :
    0 < c5CompletedCompensationMargin u t := by
  obtain ⟨sh, hsh0, hsh, hkey⟩ := regimeOne_key_holds ht htu hA
  exact c5CompletedCompensationMargin_pos_of_regimeOne_key_of_shape ht htu hA hsh0 hsh hkey

end RHTower
