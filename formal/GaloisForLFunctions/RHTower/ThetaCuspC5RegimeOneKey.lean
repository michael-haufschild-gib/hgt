import GaloisForLFunctions.RHTower.ThetaCuspC5RegimeOnePerturbation

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
  have ht2 : 0 ≤ t ^ 2 := by positivity
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
    (4 * (2 * winv) ^ 2 * z * (z + 2) + 4 * (12 * w + 2 * winv) * (z + 1))
    (zp * (8 * (2 * winv) ^ 3 * z * (z + 2) + 12 * (2 * winv) ^ 2 * (z + 1) + 4 * (12 * w + 2 * winv)))
    (24 * w * z + 6 * z * winv) ((24 * w + 12 * winv) * zp)
    (4 * (48 * winv ^ 2 * z * (z + 2) + (24 * w + 12 * winv) * (z + 1)))
    (72 * ε) (2736 * ε) (112752 * ε) (144 * ε) (2736 * ε) (112752 * ε) (4 * ε) eq

/-- Right side of the key at scale `ρ = 1`. -/
noncomputable def keyRHS (w t : ℝ) : ℝ :=
  12 * w * (24 * w - 1) * (6656 / 9 * t ^ 7 + 615872 / 945 * t ^ 9 + 50560 / 189 * t ^ 11)

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
    (a' := (12 * w + 2 * winv) * zp) (b' := 4 * (2 * winv) ^ 2 * z * (z + 2) + 4 * (12 * w + 2 * winv) * (z + 1))
    (c' := zp * (8 * (2 * winv) ^ 3 * z * (z + 2) + 12 * (2 * winv) ^ 2 * (z + 1) + 4 * (12 * w + 2 * winv)))
    (s' := 24 * w * z + 6 * z * winv) (m' := (24 * w + 12 * winv) * zp)
    (n' := 4 * (48 * winv ^ 2 * z * (z + 2) + (24 * w + 12 * winv) * (z + 1)))
    (da' := 72 * ε) (db' := 2736 * ε) (dc' := 112752 * ε) (ds' := 144 * ε) (dm' := 2736 * ε)
    (dn' := 112752 * ε) (dq' := 4 * ε) (eq := eq)
    (a'' := (12 * wb + 2 * winvb) * zpb)
    (b'' := 4 * (2 * winvb) ^ 2 * zb * (zb + 2) + 4 * (12 * wb + 2 * winvb) * (zb + 1))
    (c'' := zpb * (8 * (2 * winvb) ^ 3 * zb * (zb + 2) + 12 * (2 * winvb) ^ 2 * (zb + 1) + 4 * (12 * wb + 2 * winvb)))
    (s'' := 24 * wb * zb + 6 * zb * winvb) (m'' := (24 * wb + 12 * winvb) * zpb)
    (n'' := 4 * (48 * winvb ^ 2 * zb * (zb + 2) + (24 * wb + 12 * winvb) * (zb + 1)))
    (da'' := 72 * εb) (db'' := 2736 * εb) (dc'' := 112752 * εb) (ds'' := 144 * εb) (dm'' := 2736 * εb)
    (dn'' := 112752 * εb) (dq'' := 4 * εb) (eq' := eqb)
    ht0 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) heq0
    (by gcongr) (by gcongr) (by gcongr) (by gcongr) (by gcongr) (by gcongr)
    (by gcongr) (by gcongr) (by gcongr) (by gcongr) (by gcongr) (by gcongr) (by gcongr) heq
  -- monotonicity in `t`
  have step2 : C5LikelihoodAffineData.compensationDiffBoundE t ((12 * wb + 2 * winvb) * zpb)
      (4 * (2 * winvb) ^ 2 * zb * (zb + 2) + 4 * (12 * wb + 2 * winvb) * (zb + 1))
      (zpb * (8 * (2 * winvb) ^ 3 * zb * (zb + 2) + 12 * (2 * winvb) ^ 2 * (zb + 1) + 4 * (12 * wb + 2 * winvb)))
      (24 * wb * zb + 6 * zb * winvb) ((24 * wb + 12 * winvb) * zpb)
      (4 * (48 * winvb ^ 2 * zb * (zb + 2) + (24 * wb + 12 * winvb) * (zb + 1)))
      (72 * εb) (2736 * εb) (112752 * εb) (144 * εb) (2736 * εb) (112752 * εb) (4 * εb) eqb ≤
      C5LikelihoodAffineData.compensationDiffBoundE tb ((12 * wb + 2 * winvb) * zpb)
      (4 * (2 * winvb) ^ 2 * zb * (zb + 2) + 4 * (12 * wb + 2 * winvb) * (zb + 1))
      (zpb * (8 * (2 * winvb) ^ 3 * zb * (zb + 2) + 12 * (2 * winvb) ^ 2 * (zb + 1) + 4 * (12 * wb + 2 * winvb)))
      (24 * wb * zb + 6 * zb * winvb) ((24 * wb + 12 * winvb) * zpb)
      (4 * (48 * winvb ^ 2 * zb * (zb + 2) + (24 * wb + 12 * winvb) * (zb + 1)))
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
  have h1 : 0 ≤ 24 * wa - 1 := by linarith
  have h2 : 24 * wa - 1 ≤ 24 * w - 1 := by linarith
  have hw0 : 0 ≤ wa := by linarith
  have hpoly : 6656 / 9 * ta ^ 7 + 615872 / 945 * ta ^ 9 + 50560 / 189 * ta ^ 11 ≤
      6656 / 9 * t ^ 7 + 615872 / 945 * t ^ 9 + 50560 / 189 * t ^ 11 := by gcongr
  have hfac : 12 * wa * (24 * wa - 1) ≤ 12 * w * (24 * w - 1) :=
    mul_le_mul (by linarith) h2 h1 (by linarith)
  exact mul_le_mul hfac hpoly (by positivity) (mul_nonneg (by linarith) (by linarith))

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
    slopeDiffBound t (ρ ^ 3 * a') (ρ ^ 3 * b') (ρ ^ 3 * c') (ρ ^ 3 * s') (ρ ^ 3 * m') (ρ ^ 3 * n')
      (da' / ρ ^ 9) (db' / ρ ^ 9) (dc' / ρ ^ 9) (ds' / ρ ^ 9) (dm' / ρ ^ 9) (dn' / ρ ^ 9) ≤
    slopeDiffBound t a' b' c' s' m' n' da' db' dc' ds' dm' dn' := by
  have hρ0 : 0 < ρ := by linarith
  have hρ6 : (1 : ℝ) ≤ ρ ^ 6 := one_le_pow₀ hρ
  have hρ18 : (1 : ℝ) ≤ ρ ^ 18 := one_le_pow₀ hρ
  unfold slopeDiffBound
  have e : da' / ρ ^ 9 * (t * (ρ ^ 3 * m') + t ^ 2 * (ρ ^ 3 * n')) +
      ρ ^ 3 * a' * (t * (dm' / ρ ^ 9) + t ^ 2 * (dn' / ρ ^ 9)) +
      (da' / ρ ^ 9 + 3 * t * (db' / ρ ^ 9) + t ^ 2 * (dc' / ρ ^ 9)) * (ρ ^ 3 * s') +
      (ρ ^ 3 * a' + 3 * t * (ρ ^ 3 * b') + t ^ 2 * (ρ ^ 3 * c')) * (ds' / ρ ^ 9) +
      (da' / ρ ^ 9 * (t * (dm' / ρ ^ 9) + t ^ 2 * (dn' / ρ ^ 9)) +
        (da' / ρ ^ 9 + 3 * t * (db' / ρ ^ 9) + t ^ 2 * (dc' / ρ ^ 9)) * (ds' / ρ ^ 9)) =
      (da' * (t * m' + t ^ 2 * n') + a' * (t * dm' + t ^ 2 * dn') +
        (da' + 3 * t * db' + t ^ 2 * dc') * s' + (a' + 3 * t * b' + t ^ 2 * c') * ds') / ρ ^ 6 +
      (da' * (t * dm' + t ^ 2 * dn') + (da' + 3 * t * db' + t ^ 2 * dc') * ds') / ρ ^ 18 := by
    field_simp
    ring
  rw [e]
  have h1 : 0 ≤ da' * (t * m' + t ^ 2 * n') + a' * (t * dm' + t ^ 2 * dn') +
      (da' + 3 * t * db' + t ^ 2 * dc') * s' + (a' + 3 * t * b' + t ^ 2 * c') * ds' := by positivity
  have h2 : 0 ≤ da' * (t * dm' + t ^ 2 * dn') + (da' + 3 * t * db' + t ^ 2 * dc') * ds' := by positivity
  have := div_le_self h1 hρ6
  have := div_le_self h2 hρ18
  linarith

theorem centerDiffBound_scale {ρ t a' b' s' m' da' db' ds' dm' : ℝ} (hρ : 1 ≤ ρ)
    (ht : 0 ≤ t) (ha : 0 ≤ a') (hb : 0 ≤ b') (hs : 0 ≤ s') (hm : 0 ≤ m')
    (hda : 0 ≤ da') (hdb : 0 ≤ db') (hds : 0 ≤ ds') (hdm : 0 ≤ dm') :
    centerDiffBound t (ρ ^ 3 * a') (ρ ^ 3 * b') (ρ ^ 3 * s') (ρ ^ 3 * m')
      (da' / ρ ^ 9) (db' / ρ ^ 9) (ds' / ρ ^ 9) (dm' / ρ ^ 9) ≤
    centerDiffBound t a' b' s' m' da' db' ds' dm' / ρ ^ 6 := by
  have hρ0 : 0 < ρ := by linarith
  have hρ6 : 0 < ρ ^ 6 := by positivity
  have hρ12 : (1 : ℝ) ≤ ρ ^ 12 := one_le_pow₀ hρ
  unfold centerDiffBound
  have e : da' / ρ ^ 9 * (t * (ρ ^ 3 * m')) + ρ ^ 3 * a' * (t * (dm' / ρ ^ 9)) +
      (da' / ρ ^ 9 + t * (db' / ρ ^ 9)) * (ρ ^ 3 * s') + (ρ ^ 3 * a' + t * (ρ ^ 3 * b')) * (ds' / ρ ^ 9) +
      (da' / ρ ^ 9 * (t * (dm' / ρ ^ 9)) + (da' / ρ ^ 9 + t * (db' / ρ ^ 9)) * (ds' / ρ ^ 9)) =
      (da' * (t * m') + a' * (t * dm') + (da' + t * db') * s' + (a' + t * b') * ds') / ρ ^ 6 +
      (da' * (t * dm') + (da' + t * db') * ds') / ρ ^ 6 / ρ ^ 12 := by
    field_simp
    ring
  rw [e]
  have h2 : 0 ≤ da' * (t * dm') + (da' + t * db') * ds' := by positivity
  have h2' : 0 ≤ (da' * (t * dm') + (da' + t * db') * ds') / ρ ^ 6 := by positivity
  have := div_le_self h2' hρ12
  rw [add_div]
  linarith

theorem centerZeroBound_scale (ρ t a' b' s' m' : ℝ) :
    centerZeroBound t (ρ ^ 3 * a') (ρ ^ 3 * b') (ρ ^ 3 * s') (ρ ^ 3 * m') =
      ρ ^ 6 * centerZeroBound t a' b' s' m' := by
  unfold centerZeroBound
  ring

theorem boseZeroBoundE_scale {ρ t a' eq : ℝ} (hρ : 1 ≤ ρ) (ht : 0 ≤ t) (ha : 0 ≤ a') (heq : 0 ≤ eq) :
    boseZeroBoundE t (ρ ^ 3 * a') eq ≤ ρ ^ 3 * boseZeroBoundE t a' eq := by
  unfold boseZeroBoundE
  have hρ3 : (1 : ℝ) ≤ ρ ^ 3 := one_le_pow₀ hρ
  nlinarith [mul_nonneg ht ha, mul_nonneg (mul_nonneg ht ha) heq]

theorem boseDiffBoundE_scale {ρ t a' da' dq' eq : ℝ} (hρ : 1 ≤ ρ) (ht : 0 ≤ t) (ha : 0 ≤ a')
    (hda : 0 ≤ da') (hdq : 0 ≤ dq') (heq : 0 ≤ eq) :
    boseDiffBoundE t (ρ ^ 3 * a') (da' / ρ ^ 9) (dq' / ρ ^ 9) eq ≤ boseDiffBoundE t a' da' dq' eq / ρ ^ 6 := by
  have hρ0 : 0 < ρ := by linarith
  have hρ3 : (1 : ℝ) ≤ ρ ^ 3 := one_le_pow₀ hρ
  unfold boseDiffBoundE
  have e : 10 * t * (da' / ρ ^ 9) + 48 * t * (da' / ρ ^ 9) * eq + 192 * t * (ρ ^ 3 * a') * (dq' / ρ ^ 9) * eq =
      (10 * t * da' + 48 * t * da' * eq) / ρ ^ 6 / ρ ^ 3 + 192 * t * a' * dq' * eq / ρ ^ 6 := by
    field_simp
    ring
  rw [e, add_div]
  have h1 : 0 ≤ (10 * t * da' + 48 * t * da' * eq) / ρ ^ 6 := by positivity
  have := div_le_self h1 hρ3
  linarith

/-- **Scaling lemma.** -/
theorem compensationDiffBoundE_scale {ρ t a' b' c' s' m' n' da' db' dc' ds' dm' dn' dq' eq : ℝ}
    (hρ : 1 ≤ ρ) (ht : 0 ≤ t) (ha : 0 ≤ a') (hb : 0 ≤ b') (hc : 0 ≤ c') (hs : 0 ≤ s') (hm : 0 ≤ m')
    (hn : 0 ≤ n') (hda : 0 ≤ da') (hdb : 0 ≤ db') (hdc : 0 ≤ dc') (hds : 0 ≤ ds') (hdm : 0 ≤ dm')
    (hdn : 0 ≤ dn') (hdq : 0 ≤ dq') (heq : 0 ≤ eq) :
    compensationDiffBoundE t (ρ ^ 3 * a') (ρ ^ 3 * b') (ρ ^ 3 * c') (ρ ^ 3 * s') (ρ ^ 3 * m') (ρ ^ 3 * n')
      (da' / ρ ^ 9) (db' / ρ ^ 9) (dc' / ρ ^ 9) (ds' / ρ ^ 9) (dm' / ρ ^ 9) (dn' / ρ ^ 9) (dq' / ρ ^ 9) eq ≤
    compensationDiffBoundE t a' b' c' s' m' n' da' db' dc' ds' dm' dn' dq' eq := by
  have hρ0 : 0 < ρ := by linarith
  have hρ3 : (1 : ℝ) ≤ ρ ^ 3 := one_le_pow₀ hρ
  have hρ6 : (1 : ℝ) ≤ ρ ^ 6 := one_le_pow₀ hρ
  have hρ12 : (1 : ℝ) ≤ ρ ^ 12 := one_le_pow₀ hρ
  unfold compensationDiffBoundE
  have hS := slopeDiffBound_scale hρ ht ha hb hc hs hm hn hda hdb hdc hds hdm hdn
  have hC := centerDiffBound_scale hρ ht ha hb hs hm hda hdb hds hdm
  have hZ := centerZeroBound_scale ρ t a' b' s' m'
  have hW0 := boseZeroBoundE_scale hρ ht ha heq
  have hWd := boseDiffBoundE_scale hρ ht ha hda hdq heq
  -- nonnegativity of the pieces
  have hC0 : 0 ≤ centerDiffBound t (ρ ^ 3 * a') (ρ ^ 3 * b') (ρ ^ 3 * s') (ρ ^ 3 * m')
      (da' / ρ ^ 9) (db' / ρ ^ 9) (ds' / ρ ^ 9) (dm' / ρ ^ 9) := by
    unfold centerDiffBound; positivity
  have hCu : 0 ≤ centerDiffBound t a' b' s' m' da' db' ds' dm' := by
    unfold centerDiffBound; positivity
  have hZu : 0 ≤ centerZeroBound t a' b' s' m' := by
    unfold centerZeroBound; positivity
  have hWd0 : 0 ≤ boseDiffBoundE t (ρ ^ 3 * a') (da' / ρ ^ 9) (dq' / ρ ^ 9) eq := by
    unfold boseDiffBoundE; positivity
  have hWdu : 0 ≤ boseDiffBoundE t a' da' dq' eq := by
    unfold boseDiffBoundE; positivity
  have hW0u : 0 ≤ boseZeroBoundE t a' eq := by
    unfold boseZeroBoundE; positivity
  have hW00 : 0 ≤ boseZeroBoundE t (ρ ^ 3 * a') eq := by
    unfold boseZeroBoundE; positivity
  set Cs := centerDiffBound t (ρ ^ 3 * a') (ρ ^ 3 * b') (ρ ^ 3 * s') (ρ ^ 3 * m')
      (da' / ρ ^ 9) (db' / ρ ^ 9) (ds' / ρ ^ 9) (dm' / ρ ^ 9)
  set Cu := centerDiffBound t a' b' s' m' da' db' ds' dm'
  set Zu := centerZeroBound t a' b' s' m'
  set Wds := boseDiffBoundE t (ρ ^ 3 * a') (da' / ρ ^ 9) (dq' / ρ ^ 9) eq
  set Wdu := boseDiffBoundE t a' da' dq' eq
  set W0s := boseZeroBoundE t (ρ ^ 3 * a') eq
  set W0u := boseZeroBoundE t a' eq
  rw [hZ]
  -- second term: `Wds (ρ⁶ Zu + Cs) ≤ (Wdu/ρ⁶)(ρ⁶ Zu + Cu/ρ⁶) = Wdu Zu + Wdu Cu/ρ¹²`
  have t2 : Wds * (ρ ^ 6 * Zu + Cs) ≤ Wdu * Zu + Wdu * Cu / ρ ^ 12 := by
    have h := mul_le_mul hWd (add_le_add_left hC (ρ ^ 6 * Zu)) (by positivity) (by positivity)
    have e : Wdu / ρ ^ 6 * (ρ ^ 6 * Zu + Cu / ρ ^ 6) = Wdu * Zu + Wdu * Cu / ρ ^ 12 := by
      field_simp
      ring
    linarith
  -- third term: `W0s Cs ≤ ρ³ W0u Cu/ρ⁶ = W0u Cu / ρ³`
  have t3 : W0s * Cs ≤ W0u * Cu / ρ ^ 3 := by
    have h := mul_le_mul hW0 hC hC0 (by positivity)
    have e : ρ ^ 3 * W0u * (Cu / ρ ^ 6) = W0u * Cu / ρ ^ 3 := by
      field_simp
      ring
    linarith
  have d1 : Wdu * Cu / ρ ^ 12 ≤ Wdu * Cu := div_le_self (by positivity) hρ12
  have d2 : W0u * Cu / ρ ^ 3 ≤ W0u * Cu := div_le_self (by positivity) hρ3
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

end RHTower
