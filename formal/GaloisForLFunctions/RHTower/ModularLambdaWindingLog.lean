import GaloisForLFunctions.HTGeometry.GammaTwoSanov
import GaloisForLFunctions.RHTower.ThetaHauptmodulLogarithm
import GaloisForLFunctions.Bottcher.ModularLambdaUnconditional
import GaloisForLFunctions.Bottcher.CuspLimits

/-!
# The logarithm of the modular `λ` and its winding cocycle

The modular function `λ = (θ₂/θ₃)⁴` is holomorphic and zero-free on the upper half-plane, so it has
a holomorphic logarithm `L = lambdaLog` there (`exp_lambdaLog`). For `g ∈ Γ(2)` the function `λ` is
`g`-invariant, so `L(gτ) − L(τ)` lies in `2πiℤ`. Being continuous on a connected set, it is a
constant `2πi·c(g)` (`lambdaLog_smul_sub_eq`), and `c` is the winding homomorphism of `Γ(2)`
(`lambdaLog_smul`):

`L(gτ) = L(τ) + 2πi·w(g)`, with `w(A) = 1`, `w(B) = 0`, `w(−1) = 0` for `A = T²`, `B = S⁻¹A⁻¹S`.

* `A`: `λ(τ)e^{−iπτ} = (ϑ₂(τ/2, τ)/θ₃(τ))⁴ → 16` uniformly as `Im τ → ∞`
  (`tendsto_modularLambda_mul_exp_atImInfty`). So `L(τ) − iπτ` stays on one branch of
  `log(λe^{−iπτ})` high in the cusp, and `L(τ + 2) = L(τ) + 2πi`.
* `B`: with `σ = Sτ`, `L(S σ)` is a logarithm of `λ(Sσ) = 1 − λ(σ) → 1`, which is `2`-periodic in
  `σ`. So `L(Bτ) = L(τ)`.

Consequently, `exp(L/N)` is invariant under the winding subgroups
`Γ_N = {g ∈ Γ(2) : N ∣ w(g)}` (`exp_lambdaLog_div_smul`), which have finite index for `N ≠ 0`
(`windingSubgroup_finiteIndex`). Finally `|λ(τ)| ≤ C e^{−π Im τ}` for `Im τ ≥ 1`
(`exists_norm_modularLambda_le`).
-/

open Filter Topology Set UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower.ModularLambdaWinding

open GaloisForLFunctions.HTGeometry Bottcher

noncomputable section

/-! ### The winding subgroups -/

/-- The winding reduced modulo `N`, `Γ(2) → ℤ/N`. -/
def windingModN (N : ℕ) : Gamma 2 →* Multiplicative (ZMod N) :=
  (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod N))).comp gammaTwoWinding

/-- **The winding subgroup** `Γ_N = {g ∈ Γ(2) : N ∣ w(g)}`. -/
def windingSubgroup (N : ℕ) : Subgroup SL(2, ℤ) := (windingModN N).ker.map (Gamma 2).subtype

theorem mem_windingSubgroup {N : ℕ} {g : SL(2, ℤ)} :
    g ∈ windingSubgroup N ↔
      ∃ hg : g ∈ Gamma 2, (N : ℤ) ∣ Multiplicative.toAdd (gammaTwoWinding ⟨g, hg⟩) := by
  have key : ∀ x : Gamma 2, x ∈ (windingModN N).ker ↔
      (N : ℤ) ∣ Multiplicative.toAdd (gammaTwoWinding x) := fun x => by
    rw [MonoidHom.mem_ker, windingModN, MonoidHom.comp_apply,
      AddMonoidHom.toMultiplicative_apply_apply, ← ofAdd_zero, Equiv.apply_eq_iff_eq,
      Int.coe_castAddHom, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, (key x).1 hx⟩
  · rintro ⟨hg, hdvd⟩
    exact ⟨⟨g, hg⟩, (key _).2 hdvd, rfl⟩

/-- `Γ_N` has finite index in `SL(2, ℤ)` for `N ≠ 0`: it is the kernel of `Γ(2) → ℤ/N`. -/
instance windingSubgroup_finiteIndex (N : ℕ) [NeZero N] : (windingSubgroup N).FiniteIndex := by
  haveI : (windingModN N).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  refine ⟨?_⟩
  rw [windingSubgroup, Subgroup.index_map_subtype]
  exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero

/-! ### The logarithm of `λ` -/

theorem exists_lambdaLog : ∃ L : ℂ → ℂ, DifferentiableOn ℂ L RHTower.modUpperSet ∧
    ∀ τ ∈ RHTower.modUpperSet, Complex.exp (L τ) = modularLambda τ :=
  RHTower.exists_log_on_upperHalfPlane
    (fun _ hτ => (differentiableAt_modularLambda_of_im_pos hτ).differentiableWithinAt)
    (fun _ hτ => modularLambda_ne_zero_of_im_pos hτ)

/-- **A holomorphic logarithm of `λ` on the upper half-plane.** -/
def lambdaLog : ℂ → ℂ := Classical.choose exists_lambdaLog

theorem differentiableOn_lambdaLog : DifferentiableOn ℂ lambdaLog {τ : ℂ | 0 < τ.im} :=
  (Classical.choose_spec exists_lambdaLog).1

theorem exp_lambdaLog {τ : ℂ} (hτ : 0 < τ.im) : Complex.exp (lambdaLog τ) = modularLambda τ :=
  (Classical.choose_spec exists_lambdaLog).2 τ hτ

theorem continuousOn_lambdaLog : ContinuousOn lambdaLog {τ : ℂ | 0 < τ.im} :=
  differentiableOn_lambdaLog.continuousOn

theorem isPreconnected_im_gt (Y : ℝ) : IsPreconnected {τ : ℂ | Y < τ.im} := by
  refine Convex.isPreconnected ?_
  intro x hx y hy a b ha hb hab
  show Y < (a • x + b • y).im
  have hx' : Y < x.im := hx
  have hy' : Y < y.im := hy
  simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  have : Y = a * Y + b * Y := by rw [← add_mul, hab, one_mul]
  rcases eq_or_lt_of_le ha with h | h
  · subst h; simp at hab; subst hab; simpa using hy'
  · nlinarith [mul_lt_mul_of_pos_left hx' h, mul_le_mul_of_nonneg_left hy'.le hb]

/-- A continuous function with `exp F = 1` on a preconnected set is constant there. -/
theorem eq_of_exp_eq_one_of_isPreconnected {S : Set ℂ} (hS : IsPreconnected S) {F : ℂ → ℂ}
    (hF : ContinuousOn F S) (h1 : ∀ z ∈ S, Complex.exp (F z) = 1) {x y : ℂ} (hx : x ∈ S)
    (hy : y ∈ S) : F x = F y := by
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hint : ∀ z ∈ S, ∃ k : ℤ, F z = k * (2 * Real.pi * Complex.I) := fun z hz =>
    Complex.exp_eq_one_iff.1 (h1 z hz)
  have hφ : ∀ (z : ℂ) (k : ℤ), F z = k * (2 * Real.pi * Complex.I) → (F z / (2 * Real.pi * Complex.I)).re = k :=
    fun z k hk => by rw [hk, mul_div_assoc, div_self hc, mul_one]; simp
  have hφc : ContinuousOn (fun z => (F z / (2 * Real.pi * Complex.I)).re) S :=
    Complex.continuous_re.comp_continuousOn (hF.div_const _)
  obtain ⟨m, hm⟩ := hint x hx
  obtain ⟨n, hn⟩ := hint y hy
  suffices hmn : m = n by rw [hm, hn, hmn]
  have hhalf : ∀ z ∈ S, ∀ j : ℤ, (F z / (2 * Real.pi * Complex.I)).re ≠ (j : ℝ) + 1 / 2 := by
    intro z hz j hz'
    obtain ⟨k, hk⟩ := hint z hz
    rw [hφ z k hk] at hz'
    have h2 : ((2 * k : ℤ) : ℝ) = ((2 * j + 1 : ℤ) : ℝ) := by push_cast; linarith
    have := Int.cast_injective h2
    omega
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
    obtain ⟨z, hz, hzv⟩ := hS.intermediate_value hx hy hφc
      (show (m : ℝ) + 1 / 2 ∈ Icc _ _ by
        rw [hφ x m hm, hφ y n hn]; constructor <;> linarith)
    exact hhalf z hz m hzv
  · have hmn' : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    obtain ⟨z, hz, hzv⟩ := hS.intermediate_value hy hx hφc
      (show (n : ℝ) + 1 / 2 ∈ Icc _ _ by
        rw [hφ x m hm, hφ y n hn]; constructor <;> linarith)
    exact hhalf z hz n hzv

/-! ### Constancy of the cocycle -/

/-- The Möbius map of `g ∈ SL(2,ℤ)` on `ℂ`. -/
def sl2zMoebius (g : SL(2, ℤ)) (z : ℂ) : ℂ :=
  (((algebraMap ℤ ℝ) (g 0 0) : ℝ) * z + (((algebraMap ℤ ℝ) (g 0 1) : ℝ) : ℂ)) /
    ((((algebraMap ℤ ℝ) (g 1 0) : ℝ) : ℂ) * z + (((algebraMap ℤ ℝ) (g 1 1) : ℝ) : ℂ))

theorem coe_smul_eq_sl2zMoebius (g : SL(2, ℤ)) (τ : ℍ) : ((g • τ : ℍ) : ℂ) = sl2zMoebius g τ :=
  UpperHalfPlane.coe_specialLinearGroup_apply g τ

theorem sl2zMoebius_im_pos (g : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : 0 < (sl2zMoebius g z).im := by
  have h := (g • (⟨z, hz⟩ : ℍ)).im_pos
  rwa [UpperHalfPlane.im, coe_smul_eq_sl2zMoebius] at h

theorem continuousOn_sl2zMoebius (g : SL(2, ℤ)) : ContinuousOn (sl2zMoebius g) {z : ℂ | 0 < z.im} := by
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => ?_
  have h := UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) ⟨z, hz⟩
  simpa [UpperHalfPlane.denom] using h

/-- **The cocycle is constant**: `L(gτ) − L(τ)` does not depend on `τ ∈ ℍ`, for `g ∈ Γ(2)`. -/
theorem lambdaLog_smul_sub_eq {g : SL(2, ℤ)} (hg : g ∈ Gamma 2) (τ τ' : ℍ) :
    lambdaLog ((g • τ : ℍ) : ℂ) - lambdaLog τ = lambdaLog ((g • τ' : ℍ) : ℂ) - lambdaLog τ' := by
  rw [coe_smul_eq_sl2zMoebius, coe_smul_eq_sl2zMoebius]
  refine eq_of_exp_eq_one_of_isPreconnected (S := {z : ℂ | 0 < z.im})
    (F := fun z => lambdaLog (sl2zMoebius g z) - lambdaLog z) (by simpa using isPreconnected_im_gt 0)
    ((continuousOn_lambdaLog.comp (continuousOn_sl2zMoebius g) fun z hz => sl2zMoebius_im_pos g hz).sub
      continuousOn_lambdaLog) (fun z hz => ?_) τ.im_pos τ'.im_pos
  have hz' : 0 < z.im := hz
  rw [Complex.exp_sub, exp_lambdaLog (sl2zMoebius_im_pos g hz'), exp_lambdaLog hz',
    ← coe_smul_eq_sl2zMoebius g ⟨z, hz'⟩, modularLambda_smul hg]
  exact div_self (modularLambda_ne_zero_of_im_pos hz')

/-! ### The cusp asymptotics of `λ` -/

theorem norm_jacobiTheta₂_half_term_le {τ : ℂ} (hτ : 1 ≤ τ.im) (n : ℤ) :
    ‖jacobiTheta₂_term n (τ / 2) τ‖ ≤ Real.exp Real.pi * Real.exp (-Real.pi) ^ n.natAbs := by
  rw [norm_jacobiTheta₂_half_term, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [habs]
  have hq : |(n : ℝ)| - 1 ≤ (n : ℝ) ^ 2 + n := by
    rcases eq_or_ne n (-1) with rfl | hn
    · norm_num
    · linarith [sq_add_self_ge_abs n hn]
  have hq0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 + n := by
    rcases le_or_gt 0 n with h | h
    · have : (0 : ℝ) ≤ n := by exact_mod_cast h
      positivity
    · have : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      nlinarith
  have hpi := Real.pi_pos
  nlinarith [mul_le_mul_of_nonneg_left hτ (mul_nonneg hpi.le hq0)]

theorem tendsto_jacobiTheta₂_half_atImInfty :
    Tendsto (fun τ : ℂ => jacobiTheta₂ (τ / 2) τ) (comap Complex.im atTop) (𝓝 2) := by
  have hr0 : 0 ≤ Real.exp (-Real.pi) := (Real.exp_pos _).le
  have hr1 : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])
  have hgeo : Summable fun n : ℤ => Real.exp (-Real.pi) ^ n.natAbs := by
    have hnat := summable_geometric_of_lt_one hr0 hr1
    rw [summable_int_iff_summable_nat_and_neg]
    exact ⟨by simpa using hnat, by simpa using hnat⟩
  let c : ℤ → ℂ := fun n => if n = 0 ∨ n = -1 then 1 else 0
  have hc : ∑' n, c n = 2 := by
    have hcHS : HasSum c (∑ i ∈ ({0, -1} : Finset ℤ), c i) := by
      apply hasSum_sum_of_ne_finset_zero
      intro n hn
      simp only [c]
      rw [if_neg]
      rintro (rfl | rfl) <;> simp at hn
    rw [hcHS.tsum_eq, Finset.sum_pair (show (0 : ℤ) ≠ -1 by norm_num)]
    norm_num [c]
  suffices h : Tendsto (fun τ : ℂ => jacobiTheta₂ (τ / 2) τ) (comap Complex.im atTop)
      (𝓝 (∑' n, c n)) by rwa [hc] at h
  refine tendsto_tsum_of_dominated_convergence (hgeo.mul_left (Real.exp Real.pi)) (fun k => ?_) ?_
  · by_cases hk : k = 0 ∨ k = -1
    · rcases hk with rfl | rfl
      · simp only [jacobiTheta₂_half_term_zero, c]; simpa using tendsto_const_nhds
      · simp only [jacobiTheta₂_half_term_negone, c]; simpa using tendsto_const_nhds
    · have hck : c k = 0 := by simp only [c]; rw [if_neg hk]
      rw [hck]
      have hpos : 0 < Real.pi * ((k : ℝ) ^ 2 + k) := by
        have hne : k ≠ -1 := fun h => hk (Or.inr h)
        have hne0 : k ≠ 0 := fun h => hk (Or.inl h)
        have h1 := sq_add_self_ge_abs k hne
        have h2 : (0 : ℝ) < |(k : ℝ)| := abs_pos.2 (by exact_mod_cast hne0)
        exact mul_pos Real.pi_pos (by linarith)
      apply tendsto_zero_iff_norm_tendsto_zero.2
      simp_rw [norm_jacobiTheta₂_half_term]
      have : Tendsto (fun τ : ℂ => -Real.pi * ((k : ℝ) ^ 2 + k) * τ.im) (comap Complex.im atTop)
          atBot := by
        have hi : Tendsto Complex.im (comap Complex.im atTop) atTop := tendsto_comap
        refine (tendsto_neg_atTop_atBot.comp (hi.const_mul_atTop hpos)).congr fun τ => ?_
        simp only [Function.comp]
        ring
      exact Real.tendsto_exp_atBot.comp this
  · filter_upwards [tendsto_comap.eventually (eventually_ge_atTop (1 : ℝ))] with τ hτ k
    exact norm_jacobiTheta₂_half_term_le hτ k

theorem modularLambda_mul_exp_eq (τ : ℂ) :
    modularLambda τ * Complex.exp (-(Real.pi * Complex.I * τ)) =
      (jacobiTheta₂ (τ / 2) τ / thetaThree τ) ^ 4 := by
  rw [modularLambda, thetaTwo, mul_div_assoc, mul_pow, mul_assoc, mul_comm _ (Complex.exp _),
    ← mul_assoc, ← Complex.exp_nat_mul, ← Complex.exp_add]
  rw [show ((4 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I * τ / 4) + -(Real.pi * Complex.I * τ) = 0 by push_cast; ring,
    Complex.exp_zero, one_mul]

/-- **`λ(τ) e^{−iπτ} → 16`** uniformly as `Im τ → ∞`. -/
theorem tendsto_modularLambda_mul_exp_atImInfty :
    Tendsto (fun τ : ℂ => modularLambda τ * Complex.exp (-(Real.pi * Complex.I * τ)))
      (comap Complex.im atTop) (𝓝 16) := by
  simp_rw [modularLambda_mul_exp_eq]
  have h := (tendsto_jacobiTheta₂_half_atImInfty.div tendsto_thetaThree_atImInfty one_ne_zero).pow 4
  norm_num at h
  exact h

theorem exists_im_ge_mem_slitPlane {f : ℂ → ℂ} {a : ℂ} (ha : a ∈ Complex.slitPlane)
    (hf : Tendsto f (comap Complex.im atTop) (𝓝 a)) :
    ∃ Y : ℝ, 1 ≤ Y ∧ ∀ z : ℂ, Y ≤ z.im → f z ∈ Complex.slitPlane := by
  have h := hf.eventually (Complex.isOpen_slitPlane.mem_nhds ha)
  rw [Filter.eventually_comap, eventually_atTop] at h
  obtain ⟨Y, hY⟩ := h
  exact ⟨max Y 1, le_max_right _ _, fun z hz => hY z.im (le_trans (le_max_left _ _) hz) z rfl⟩

/-! ### The cocycle on the generators -/

/-- **`L(τ + 2) = L(τ) + 2πi`** high in the cusp. -/
theorem exists_lambdaLog_add_two :
    ∃ Y : ℝ, 0 < Y ∧ ∀ z : ℂ, Y < z.im → lambdaLog (z + 2) = lambdaLog z + 2 * Real.pi * Complex.I := by
  obtain ⟨Y, hY1, hY⟩ := exists_im_ge_mem_slitPlane (by norm_num [Complex.slitPlane])
    tendsto_modularLambda_mul_exp_atImInfty
  refine ⟨Y, by linarith, fun z hz => ?_⟩
  let G : ℂ → ℂ := fun τ => modularLambda τ * Complex.exp (-(Real.pi * Complex.I * τ))
  have hGc : ContinuousOn G {τ : ℂ | Y < τ.im} := fun τ hτ =>
    ((differentiableAt_modularLambda_of_im_pos (show 0 < τ.im by
      have : Y < τ.im := hτ; linarith)).continuousAt.mul
      (by fun_prop : Continuous fun τ : ℂ => Complex.exp (-(Real.pi * Complex.I * τ))).continuousAt
      ).continuousWithinAt
  have hGslit : ∀ τ ∈ {τ : ℂ | Y < τ.im}, G τ ∈ Complex.slitPlane := fun τ hτ => hY τ (le_of_lt hτ)
  have hF := eq_of_exp_eq_one_of_isPreconnected (isPreconnected_im_gt Y)
    (F := fun τ => lambdaLog τ - Real.pi * Complex.I * τ - Complex.log (G τ))
    (((continuousOn_lambdaLog.mono fun τ hτ => by
        show 0 < τ.im; have : Y < τ.im := hτ; linarith).sub (by fun_prop)).sub
      (ContinuousOn.clog hGc hGslit))
    (fun τ hτ => by
      have hτ0 : 0 < τ.im := by have : Y < τ.im := hτ; linarith
      rw [Complex.exp_sub, Complex.exp_sub, exp_lambdaLog hτ0,
        Complex.exp_log (Complex.slitPlane_ne_zero (hGslit τ hτ))]
      simp only [G]
      rw [Complex.exp_neg]
      field_simp [modularLambda_ne_zero_of_im_pos hτ0, Complex.exp_ne_zero])
    (show Y < z.im from hz) (show Y < (z + 2).im by simpa using hz)
  have he : Complex.exp (-(2 * Real.pi * Complex.I)) = 1 := by
    rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  have hG2 : G (z + 2) = G z := by
    simp only [G]
    rw [modularLambda_add_two, show -(↑Real.pi * Complex.I * (z + 2)) =
      -(↑Real.pi * Complex.I * z) + -(2 * ↑Real.pi * Complex.I) by ring, Complex.exp_add, he,
      mul_one]
  rw [hG2] at hF
  linear_combination -hF

theorem tendsto_one_sub_modularLambda_atImInfty' :
    Tendsto (fun τ => 1 - modularLambda τ) (comap Complex.im atTop) (𝓝 1) := by
  have h : Tendsto (fun τ => (thetaTwo τ / thetaThree τ) ^ 4) (comap Complex.im atTop)
      (𝓝 ((0 / 1) ^ 4)) :=
    (tendsto_thetaTwo_atImInfty.div tendsto_thetaThree_atImInfty (by norm_num)).pow 4
  have h' : Tendsto modularLambda (comap Complex.im atTop) (𝓝 0) := by
    rw [show modularLambda = fun τ => (thetaTwo τ / thetaThree τ) ^ 4 from rfl]
    simpa using h
  simpa using (tendsto_const_nhds (x := (1 : ℂ))).sub h'

theorem im_neg_one_div_pos {τ : ℂ} (hτ : 0 < τ.im) : 0 < (-1 / τ).im := by
  have hτ0 : τ ≠ 0 := fun h => by rw [h] at hτ; simp at hτ
  rw [neg_div, Complex.neg_im, one_div, Complex.inv_im, neg_div, neg_neg]
  exact div_pos hτ (Complex.normSq_pos.2 hτ0)

/-- High in the cusp, `L(S(σ − 2)) = L(Sσ)`, because `λ(Sσ) = 1 − λ(σ)` stays
near `1` and is `2`-periodic. -/
theorem exists_lambdaLog_S_sub_two :
    ∃ Y : ℝ, 0 < Y ∧ ∀ z : ℂ, Y < z.im →
      lambdaLog (-1 / (z - 2)) = lambdaLog (-1 / z) := by
  obtain ⟨Y, hY1, hY⟩ := exists_im_ge_mem_slitPlane (by norm_num [Complex.slitPlane])
    tendsto_one_sub_modularLambda_atImInfty'
  refine ⟨Y, by linarith, fun z hz => ?_⟩
  have hpos : ∀ τ ∈ {τ : ℂ | Y < τ.im}, 0 < τ.im := fun τ hτ => by
    have : Y < τ.im := hτ; linarith
  have hS : ∀ τ ∈ {τ : ℂ | Y < τ.im}, 0 < (-1 / τ).im := fun τ hτ => im_neg_one_div_pos (hpos τ hτ)
  have hcS : ContinuousOn (fun τ : ℂ => -1 / τ) {τ : ℂ | Y < τ.im} :=
    continuousOn_const.div continuousOn_id fun τ hτ h0 => by
      have := hpos τ hτ; rw [h0] at this; simp at this
  have hlc : ContinuousOn (fun τ => 1 - modularLambda τ) {τ : ℂ | Y < τ.im} := fun τ hτ =>
    (continuousAt_const.sub (differentiableAt_modularLambda_of_im_pos
      (hpos τ hτ)).continuousAt).continuousWithinAt
  have hslit : ∀ τ ∈ {τ : ℂ | Y < τ.im}, 1 - modularLambda τ ∈ Complex.slitPlane := fun τ hτ =>
    hY τ (le_of_lt hτ)
  have hF := eq_of_exp_eq_one_of_isPreconnected (isPreconnected_im_gt Y)
    (F := fun τ => lambdaLog (-1 / τ) - Complex.log (1 - modularLambda τ))
    ((continuousOn_lambdaLog.comp hcS hS).sub (ContinuousOn.clog hlc hslit))
    (fun τ hτ => by
      rw [Complex.exp_sub, exp_lambdaLog (hS τ hτ), modularLambda_S' (hpos τ hτ),
        Complex.exp_log (Complex.slitPlane_ne_zero (hslit τ hτ))]
      exact div_self (Complex.slitPlane_ne_zero (hslit τ hτ)))
    (show Y < (z - 2).im by simpa using hz) (show Y < z.im from hz)
  have h2 : modularLambda (z - 2) = modularLambda z := by
    have := modularLambda_add_two (z - 2)
    rwa [sub_add_cancel, eq_comm] at this
  rw [h2] at hF
  linear_combination hF

theorem coe_sanovA_smul (τ : ℍ) : ((sanovA • τ : ℍ) : ℂ) = τ + 2 := by
  rw [sanovA_eq, show (ModularGroup.T ^ 2 : SL(2, ℤ)) = ModularGroup.T ^ (2 : ℤ) by norm_cast,
    ModularGroup.coe_T_zpow_smul_eq]
  push_cast
  ring

/-- **The generator `A = T²`**: `L(Aτ) = L(τ) + 2πi`. -/
theorem lambdaLog_sanovA_smul (τ : ℍ) :
    lambdaLog ((sanovA • τ : ℍ) : ℂ) = lambdaLog τ + 2 * Real.pi * Complex.I := by
  obtain ⟨Y, hY, hYA⟩ := exists_lambdaLog_add_two
  let τ₀ : ℍ := ⟨(Y + 1 : ℝ) * Complex.I, by simp; linarith⟩
  have h0 := hYA (τ₀ : ℂ) (by simp [τ₀])
  rw [← coe_sanovA_smul] at h0
  have hc := lambdaLog_smul_sub_eq sanovA_mem τ τ₀
  linear_combination hc + h0

theorem coe_modularS_smul (τ : ℍ) : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / τ := by
  rw [UpperHalfPlane.modular_S_smul]
  simp [neg_div, inv_neg, one_div]

/-- **The generator `B = S⁻¹A⁻¹S`**: `L(Bτ) = L(τ)`. -/
theorem lambdaLog_sanovB_smul (τ : ℍ) :
    lambdaLog ((sanovB • τ : ℍ) : ℂ) = lambdaLog τ := by
  obtain ⟨Y, hY, hYB⟩ := exists_lambdaLog_S_sub_two
  let σ₀ : ℍ := ⟨(Y + 1 : ℝ) * Complex.I, by simp; linarith⟩
  -- `τ₀ = S⁻¹σ₀` and `Bτ₀ = S⁻¹(σ₀ − 2)`
  have hSinv : ∀ w : ℍ, ((ModularGroup.S⁻¹ • w : ℍ) : ℂ) = -1 / w := by
    intro w
    have hSS : ModularGroup.S * ModularGroup.S = -1 := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.S_mul_S_eq,
        Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one])
    have hSw : ModularGroup.S⁻¹ • w = ModularGroup.S • w := by
      rw [inv_smul_eq_iff, ← mul_smul, hSS, ModularGroup.SL_neg_smul, one_smul]
    rw [hSw, coe_modularS_smul]
  have hB : sanovB • (ModularGroup.S⁻¹ • σ₀) = ModularGroup.S⁻¹ • (sanovA⁻¹ • σ₀) := by
    rw [sanovB_eq_conj, mul_smul, mul_smul, smul_inv_smul]
  have hA : ((sanovA⁻¹ • σ₀ : ℍ) : ℂ) = (σ₀ : ℂ) - 2 := by
    have h := coe_sanovA_smul (sanovA⁻¹ • σ₀)
    rw [smul_inv_smul] at h
    rw [h]; ring
  have h0 := hYB (σ₀ : ℂ) (by simp [σ₀])
  have hc := lambdaLog_smul_sub_eq sanovB_mem τ (ModularGroup.S⁻¹ • σ₀)
  rw [hB, hSinv, hSinv, hA] at hc
  linear_combination hc + h0

/-! ### The winding cocycle -/

/-- **The winding cocycle of `log λ`**: `L(gτ) = L(τ) + 2πi·w(g)` for `g ∈ Γ(2)`. -/
theorem lambdaLog_smul {g : SL(2, ℤ)} (hg : g ∈ Gamma 2) (τ : ℍ) :
    lambdaLog ((g • τ : ℍ) : ℂ) =
      lambdaLog τ + 2 * Real.pi * Complex.I *
        ((Multiplicative.toAdd (gammaTwoWinding ⟨g, hg⟩) : ℤ) : ℂ) := by
  have hg' := hg
  rw [gammaTwo_eq_closure] at hg'
  induction hg' using Subgroup.closure_induction generalizing τ with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · rw [show (⟨sanovA, hg⟩ : Gamma 2) = ⟨sanovA, sanovA_mem⟩ from rfl, gammaTwoWinding_sanovA,
        lambdaLog_sanovA_smul]
      simp
    · rw [show (⟨sanovB, hg⟩ : Gamma 2) = ⟨sanovB, sanovB_mem⟩ from rfl, gammaTwoWinding_sanovB,
        lambdaLog_sanovB_smul]
      simp
    · rw [show (⟨-1, hg⟩ : Gamma 2) = ⟨-1, Bottcher.negOne_mem_Gamma2⟩ from rfl,
        gammaTwoWinding_neg_one, ModularGroup.SL_neg_smul, one_smul]
      simp
  | one =>
    rw [show (⟨1, hg⟩ : Gamma 2) = 1 from rfl, map_one, one_smul]
    simp
  | mul x y hx hy ihx ihy =>
    have hxg : x ∈ Gamma 2 := by rw [gammaTwo_eq_closure]; exact hx
    have hyg : y ∈ Gamma 2 := by rw [gammaTwo_eq_closure]; exact hy
    rw [show (⟨x * y, hg⟩ : Gamma 2) = ⟨x, hxg⟩ * ⟨y, hyg⟩ from rfl, map_mul, toAdd_mul, mul_smul,
      ihx hxg, ihy hyg]
    push_cast
    ring
  | inv x hx ihx =>
    have hxg : x ∈ Gamma 2 := by rw [gammaTwo_eq_closure]; exact hx
    have h := ihx hxg (x⁻¹ • τ)
    rw [smul_inv_smul] at h
    rw [show (⟨x⁻¹, hg⟩ : Gamma 2) = (⟨x, hxg⟩ : Gamma 2)⁻¹ from rfl, map_inv, toAdd_inv]
    push_cast
    linear_combination -h

/-- **`exp(L/N)` is invariant under `Γ_N`.** -/
theorem exp_lambdaLog_div_smul {N : ℕ} {g : SL(2, ℤ)} (hg : g ∈ windingSubgroup N) (τ : ℍ) :
    Complex.exp (lambdaLog ((g • τ : ℍ) : ℂ) / N) = Complex.exp (lambdaLog τ / N) := by
  obtain ⟨hg2, k, hk⟩ := mem_windingSubgroup.1 hg
  rw [lambdaLog_smul hg2, hk]
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    rw [show (lambdaLog τ + 2 * Real.pi * Complex.I * (((N : ℤ) * k : ℤ) : ℂ)) / N =
      lambdaLog τ / N + (k : ℂ) * (2 * Real.pi * Complex.I) by push_cast; field_simp,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ### Decay at the cusp -/

/-- **`|λ(τ)| ≤ C e^{−π Im τ}` for `Im τ ≥ 1`.** -/
theorem exists_norm_modularLambda_le :
    ∃ C : ℝ, ∀ τ : ℂ, 1 ≤ τ.im → ‖modularLambda τ‖ ≤ C * Real.exp (-Real.pi * τ.im) := by
  have hr0 : 0 ≤ Real.exp (-Real.pi) := (Real.exp_pos _).le
  have hr1 : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])
  have hgeo : Summable fun n : ℤ => Real.exp (-Real.pi) ^ n.natAbs := by
    have hnat := summable_geometric_of_lt_one hr0 hr1
    rw [summable_int_iff_summable_nat_and_neg]
    exact ⟨by simpa using hnat, by simpa using hnat⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = Real.exp Real.pi * ∑' n : ℤ, Real.exp (-Real.pi) ^ n.natAbs :=
    ⟨_, rfl⟩
  -- `|θ₃| ≥ 1/2` for `Im τ ≥ 1`
  have hθ3 : ∀ τ : ℂ, 1 ≤ τ.im → (1 / 2 : ℝ) ≤ ‖thetaThree τ‖ := by
    intro τ hτ
    have h := norm_jacobiTheta_sub_one_le (show 0 < τ.im by linarith)
    have he : Real.exp (-Real.pi * τ.im) ≤ Real.exp (-Real.pi) :=
      Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
    have hsmall : Real.exp (-Real.pi) ≤ 1 / 5 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have := Real.quadratic_le_exp_of_nonneg Real.pi_pos.le
      nlinarith [Real.pi_gt_three]
    have hq : 2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) ≤ 1 / 2 := by
      have hpos : 0 < 1 - Real.exp (-Real.pi * τ.im) := by linarith
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith
    have h' : ‖thetaThree τ - 1‖ ≤ 1 / 2 := by
      rw [thetaThree, ← jacobiTheta_eq_jacobiTheta₂]; exact h.trans hq
    have := norm_sub_norm_le (1 : ℂ) (thetaThree τ)
    rw [norm_one, norm_sub_rev] at this
    linarith
  refine ⟨(2 * B) ^ 4, fun τ hτ => ?_⟩
  have hjt : ‖jacobiTheta₂ (τ / 2) τ‖ ≤ B := by
    rw [hB]
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (norm_jacobiTheta₂_half_term_le hτ) (hgeo.mul_left _)
    · rw [← tsum_mul_left]
      exact Summable.tsum_le_tsum (norm_jacobiTheta₂_half_term_le hτ)
        (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_jacobiTheta₂_half_term_le hτ)
          (hgeo.mul_left _)) (hgeo.mul_left _)
  have hlam : modularLambda τ = Complex.exp (Real.pi * Complex.I * τ) *
      (jacobiTheta₂ (τ / 2) τ / thetaThree τ) ^ 4 := by
    rw [← modularLambda_mul_exp_eq, mul_comm (modularLambda τ), ← mul_assoc, ← Complex.exp_add,
      add_neg_cancel, Complex.exp_zero, one_mul]
  have hexp : ‖Complex.exp (Real.pi * Complex.I * τ)‖ = Real.exp (-Real.pi * τ.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have h3 := hθ3 τ hτ
  have hq : ‖jacobiTheta₂ (τ / 2) τ / thetaThree τ‖ ≤ 2 * B := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) hjt
    nlinarith
  rw [hlam, norm_mul, hexp, norm_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hq 4) (Real.exp_pos _).le

end

end GaloisForLFunctions.RHTower.ModularLambdaWinding
